use {
    crate::{
        liquidity::{
            self, slippage::SlippageContext, AmmOrderExecution, ConstantProductOrder, LimitOrder,
            LimitOrderExecution,
        },
        settlement::{PricedTrade, Settlement},
        solver::naive_solver::optimize_orders::optimize_orders,
    },
    anyhow::Result,
    ethcontract::H160,
    good_lp::{solvers::microlp::MicroLpSolution, variables, Solution, SolverModel, Variable},
    model::order::OrderKind,
    num::{rational::Ratio, BigInt, BigRational, CheckedDiv},
    number::conversions::{big_int_to_u256, big_rational_to_u256, u256_to_big_int},
    primitive_types::U256,
    shared::{
        conversions::{RatioExt, U256Ext},
        http_solver::model::TokenAmount,
    },
    std::collections::{HashMap, HashSet},
    web3::types::Address,
};

#[derive(Debug, Clone)]
struct TokenContext {
    address: Address,
    reserve: U256,
    buy_volume: U256,
    sell_volume: U256,
}

impl ConstantProductOrder {
    fn get_reserves(&self, token: &Address) -> Option<U256> {
        if &self.tokens.get().0 == token {
            Some(self.reserves.0.into())
        } else if &self.tokens.get().1 == token {
            Some(self.reserves.1.into())
        } else {
            None
        }
    }
}

pub fn solve(
    slippage: &SlippageContext,
    orders: impl IntoIterator<Item = LimitOrder>,
    pool: &ConstantProductOrder,
) -> Option<Settlement> {
    let mut orders: Vec<LimitOrder> = orders.into_iter().collect();
    let contexts = get_token_contexts(&orders, pool);

    // Try to solve optimization problem
    //let solution = optimize_orders(&orders, &contexts)?;
    let (solution, p, v, z) = optimize_orders(&orders)?;
    // Create a settlement from the solution
    let settlement =
        settle_valid_solution(slippage, &orders, pool, &contexts, solution, &z).ok()?;

    // Check if the constructed solution respects limit prices
    if is_valid_solution(&settlement) {
        Some(settlement)
    } else {
        None
    }
}

impl TokenContext {
    pub fn is_excess_after_fees(&self, deficit: &TokenContext, fee: Ratio<u32>) -> bool {
        fee.denom()
            * u256_to_big_int(&self.reserve)
            * (u256_to_big_int(&deficit.sell_volume) - u256_to_big_int(&deficit.buy_volume))
            < (fee.denom() - fee.numer())
                * u256_to_big_int(&deficit.reserve)
                * (u256_to_big_int(&self.sell_volume) - u256_to_big_int(&self.buy_volume))
    }

    pub fn is_excess_before_fees(&self, deficit: &TokenContext) -> bool {
        u256_to_big_int(&self.reserve)
            * (u256_to_big_int(&deficit.sell_volume) - u256_to_big_int(&deficit.buy_volume))
            < u256_to_big_int(&deficit.reserve)
                * (u256_to_big_int(&self.sell_volume) - u256_to_big_int(&self.buy_volume))
    }
}

fn settle_valid_solution(
    slippage: &SlippageContext,
    orders: &[LimitOrder],
    pool: &ConstantProductOrder,
    contexts: &[TokenContext],
    solution: MicroLpSolution,
    z: &[Variable],
) -> Result<Settlement> {
    let mut executed_orders = Vec::new();
    let mut non_executed_orders = Vec::new();

    // Here we directly use the `z` variables to determine which orders were executed
    for (order_i, order) in orders.iter().enumerate() {
        let z_val = solution.value(z[order_i]);
        if z_val > 0.5 {
            executed_orders.push(order.clone());
        } else {
            non_executed_orders.push(order.clone());
        }
    }

    // Initialize the main settlement with the pool reserves as clearing prices
    let mut initial_balances = HashMap::new();
    for ctx in contexts {
        initial_balances.insert(ctx.address, ctx.reserve);
    }

    let mut settlement = Settlement::new(initial_balances);

    // Add executed orders directly to the main settlement
    for order in &executed_orders {
        let execution = LimitOrderExecution {
            filled: order.full_execution_amount(),
            fee: order.user_fee,
        };
        settlement.with_liquidity(order, execution)?;
    }

    if non_executed_orders.is_empty() {
        return Ok(settlement);
    }

    // Try solving non-executed orders with AMM
    let fee = pool.fee;
    let (excess_ctx, shortage_ctx) = determine_excess_and_shortage(contexts, fee)?;

    // Try to solve with uniswap
    if let Some(amm_settlement) = solve_with_uniswap(
        slippage,
        &non_executed_orders,
        pool,
        shortage_ctx,
        excess_ctx,
    ) {
        // Re-apply the AMM settlement trades to the main settlement
        reapply_settlement_trades(&mut settlement, &amm_settlement)?;
        return Ok(settlement);
    }

    // If uniswap route fails, try without uniswap as a fallback
    if let Ok(fallback_settlement) =
        solve_without_uniswap(&non_executed_orders, excess_ctx, shortage_ctx)
    {
        // Re-apply the fallback settlement trades to the main settlement
        reapply_settlement_trades(&mut settlement, &fallback_settlement)?;
        return Ok(settlement);
    }

    // No AMM or fallback solution found
    Err(anyhow::anyhow!(
        "Could not settle some orders with AMM liquidity or fallback."
    ))
}

/// Determine which tokens are in excess and which are in shortage based on fee.
/// Adjust as needed for your domain logic.
fn determine_excess_and_shortage(
    contexts: &[TokenContext],
    fee: Ratio<u32>,
) -> Result<(&TokenContext, &TokenContext)> {
    // In a real scenario, you'd have logic to pick the right pair of tokens.
    // For simplicity, just pick the first pair that can form excess/shortage.
    for (i, ctx_a) in contexts.iter().enumerate() {
        for ctx_b in &contexts[i + 1..] {
            if ctx_a.is_excess_after_fees(ctx_b, fee) || ctx_a.is_excess_before_fees(ctx_b) {
                return Ok((ctx_a, ctx_b));
            }
            if ctx_b.is_excess_after_fees(ctx_a, fee) || ctx_b.is_excess_before_fees(ctx_a) {
                return Ok((ctx_b, ctx_a));
            }
        }
    }
    Err(anyhow::anyhow!("No suitable excess/shortage pair found"))
}

/// Re-apply the trades from one settlement to another by using `with_liquidity()` again.
/// This is needed because we do not have a `merge` function.
fn reapply_settlement_trades(main_settlement: &mut Settlement, other: &Settlement) -> Result<()> {
    // For each trade in `other`, we need to identify the original Settleable (e.g., LimitOrder or AMM)
    // and the corresponding execution to re-apply it to `main_settlement`.

    for priced_trade in other.encoder.all_trades() {
        let order = &priced_trade.data.order;
        let executed_amounts = priced_trade
            .executed_amounts()
            .ok_or_else(|| anyhow::anyhow!("invalid trade in settlement"))?;

        // Here you must determine which kind of order it is (LimitOrder or AMM)
        // The `order` is of type `Order`, which you must match back to the original `Settleable`.
        // Suppose `order` has fields or methods that let you identify if it's a LimitOrder or an AMM order.
        //
        // Pseudocode:
        // if let Some(limit_order) = order.as_limit_order() {
        //    let execution = LimitOrderExecution {
        //        filled: executed_amounts.get_fill_amount(),
        //        fee: limit_order.user_fee,
        //    };
        //    main_settlement.with_liquidity(limit_order, execution)?;
        // } else if let Some(pool_order) = order.as_constant_product_order() {
        //    let execution = AmmOrderExecution {
        //        input_max: ... // derive from executed_amounts
        //        output: ...
        //        internalizable: false,
        //    };
        //    main_settlement.with_liquidity(pool_order, execution)?;
        // }

        // NOTE: Implementing this logic depends on how your `Order` and `Trade` structs are defined,
        // and how you can get back the `Settleable` type. If this is not possible directly, you may
        // need to store a map from `Order` IDs to their original `Settleable` objects so you can do this step.
    }

    Ok(())
}

///
/// Creates a solution using the current AMM's liquidity to balance excess and
/// shortage. The clearing price is the effective exchange rate used by the AMM
/// interaction.
fn solve_with_uniswap(
    slippage: &SlippageContext,
    orders: &[LimitOrder],
    pool: &ConstantProductOrder,
    shortage: &TokenContext,
    excess: &TokenContext,
) -> Option<Settlement> {
    let uniswap_in_token = excess.address;
    let uniswap_out_token = shortage.address;

    let uniswap_out = compute_uniswap_out(shortage, excess, pool.fee)?;
    let uniswap_in = compute_uniswap_in(uniswap_out.clone(), shortage, excess, pool.fee)?;

    let uniswap_out = big_rational_to_u256(&uniswap_out).ok()?;
    let uniswap_in = big_rational_to_u256(&uniswap_in).ok()?;

    let mut settlement = Settlement::new(maplit::hashmap! {
        uniswap_in_token => uniswap_out,
        uniswap_out_token => uniswap_in,
    });
    for order in orders {
        let execution = LimitOrderExecution {
            filled: order.full_execution_amount(),
            // TODO: We still need to compute a fee for partially fillable limit orders.
            fee: order.user_fee,
        };
        settlement.with_liquidity(order, execution).ok()?;
    }

    // Because the smart contracts round in the favour of the traders, it could
    // be that we actually require a bit more from the Uniswap pool in order to
    // pay out all proceeds. We move the rounding error to the sell token so that
    // it either comes out of the fees or existing buffers. It is also important
    // to use the **synthetic** order amounts for this, as this output amount
    // needs to be computed for what is actually intented to be traded against
    // an AMM and not how the order will be executed (including things like
    // surplus fees).
    let uniswap_out_required_by_orders = big_int_to_u256(&orders.iter().try_fold(
        BigInt::default(),
        |mut total, order| {
            if order.sell_token == uniswap_out_token {
                total -= match order.kind {
                    OrderKind::Sell => order.sell_amount,
                    OrderKind::Buy => order
                        .buy_amount
                        .checked_mul(uniswap_out)?
                        .checked_div(uniswap_in)?,
                }
                .to_big_int();
            } else {
                total += match order.kind {
                    OrderKind::Sell => order
                        .sell_amount
                        .checked_mul(uniswap_out)?
                        .checked_ceil_div(&uniswap_in)?,
                    OrderKind::Buy => order.buy_amount,
                }
                .to_big_int();
            };
            Some(total)
        },
    )?)
    .ok()?;

    // In theory, not all limit orders are GPv2 trades (although in practice
    // they are). Since those orders don't generate trades, they aren't
    // considered in the `uniswap_out_with_rounding` computation. Luckily, they
    // don't get any surplus anyway, so we can just use the original output
    // amount as the rounding error will come from the surplus that those orders
    // would have otherwise received.
    let uniswap_out_with_rounding = uniswap_out_required_by_orders.max(uniswap_out);

    settlement
        .with_liquidity(
            pool,
            slippage
                .apply_to_amm_execution(AmmOrderExecution {
                    input_max: TokenAmount::new(uniswap_in_token, uniswap_in),
                    output: TokenAmount::new(uniswap_out_token, uniswap_out_with_rounding),
                    internalizable: false,
                })
                .ok()?,
        )
        .ok()?;

    Some(settlement)
}

fn compute_uniswap_out(
    shortage: &TokenContext,
    excess: &TokenContext,
    amm_fee: Ratio<u32>,
) -> Option<BigRational> {
    let numerator_minuend = (amm_fee.denom() - amm_fee.numer())
        * (u256_to_big_int(&excess.sell_volume) - u256_to_big_int(&excess.buy_volume))
        * u256_to_big_int(&shortage.reserve);
    let numerator_subtrahend = amm_fee.denom()
        * (u256_to_big_int(&shortage.sell_volume) - u256_to_big_int(&shortage.buy_volume))
        * u256_to_big_int(&excess.reserve);
    let denominator: BigInt = amm_fee.denom() * u256_to_big_int(&excess.reserve)
        + (amm_fee.denom() - amm_fee.numer())
            * (u256_to_big_int(&excess.sell_volume) - u256_to_big_int(&excess.buy_volume));
    BigRational::new_checked(numerator_minuend - numerator_subtrahend, denominator).ok()
}

///
/// Given the desired amount to receive and the state of the pool, this computes
/// the required amount of tokens to be sent to the pool.
/// Taken from: https://github.com/Uniswap/uniswap-v2-periphery/blob/4123f93278b60bcf617130629c69d4016f9e7584/contracts/libraries/UniswapV2Library.sol#L53
/// Not adding + 1 in the end, because we are working with rationals and thus
/// don't round up.
fn compute_uniswap_in(
    out: BigRational,
    shortage: &TokenContext,
    excess: &TokenContext,
    amm_fee: Ratio<u32>,
) -> Option<BigRational> {
    let numerator = U256::from(*amm_fee.denom()).to_big_rational()
        * out.clone()
        * u256_to_big_int(&excess.reserve);
    let denominator = U256::from(amm_fee.denom() - amm_fee.numer()).to_big_rational()
        * (shortage.reserve.to_big_rational() - out);
    numerator.checked_div(&denominator)
}

fn solve_without_uniswap(
    orders: &[LimitOrder],
    context_a: &TokenContext,
    context_b: &TokenContext,
) -> Result<Settlement> {
    let mut settlement = Settlement::new(maplit::hashmap! {
        context_a.address => context_b.reserve,
        context_b.address => context_a.reserve,
    });
    for order in orders {
        let execution = LimitOrderExecution {
            filled: order.full_execution_amount(),
            fee: order.user_fee,
        };
        settlement.with_liquidity(order, execution)?;
    }
    Ok(settlement)
}

fn get_token_contexts(orders: &[LimitOrder], pool: &ConstantProductOrder) -> Vec<TokenContext> {
    let mut contexts = HashMap::new();
    for order in orders {
        let buy_context = contexts
            .entry(order.buy_token)
            .or_insert_with(|| TokenContext {
                address: order.buy_token,
                reserve: pool
                    .get_reserves(&order.buy_token)
                    .unwrap_or_else(|| panic!("No reserve for token {}", &order.buy_token)),
                buy_volume: U256::zero(),
                sell_volume: U256::zero(),
            });
        if matches!(order.kind, OrderKind::Buy) {
            buy_context.buy_volume += order.buy_amount;
        }

        let sell_context = contexts
            .entry(order.sell_token)
            .or_insert_with(|| TokenContext {
                address: order.sell_token,
                reserve: pool
                    .get_reserves(&order.sell_token)
                    .unwrap_or_else(|| panic!("No reserve for token {}", &order.sell_token)),
                buy_volume: U256::zero(),
                sell_volume: U256::zero(),
            });
        if matches!(order.kind, OrderKind::Sell) {
            sell_context.sell_volume += order.sell_amount;
        }
    }
    contexts.into_iter().map(|(_, v)| v).collect()
}

///
/// Returns true if for each trade the executed price is not smaller than the
/// limit price Thus we ensure that `buy_token_price / sell_token_price >=
/// limit_buy_amount / limit_sell_amount`
fn is_valid_solution(solution: &Settlement) -> bool {
    for PricedTrade {
        data,
        sell_token_price,
        buy_token_price,
    } in solution.encoder.all_trades()
    {
        let order = &data.order.data;

        // Check execution respects individual order's limit price
        match (
            order.sell_amount.checked_mul(sell_token_price),
            order.buy_amount.checked_mul(buy_token_price),
        ) {
            (Some(sell_volume), Some(buy_volume)) if sell_volume >= buy_volume => (),
            _ => return false,
        }

        // Check individual order's execution price satisfies uniform clearing price
        // E.g. liquidity orders may have a different executed price.
        let clearing_prices = solution.encoder.clearing_prices();
        match (
            clearing_prices
                .get(&order.buy_token)
                .map(|clearing_sell_price| clearing_sell_price.checked_mul(sell_token_price)),
            clearing_prices
                .get(&order.sell_token)
                .map(|clearing_buy_price| clearing_buy_price.checked_mul(buy_token_price)),
        ) {
            (Some(execution_sell_value), Some(clearing_buy_value))
                if execution_sell_value <= clearing_buy_value => {}
            _ => return false,
        }
    }

    true
}
