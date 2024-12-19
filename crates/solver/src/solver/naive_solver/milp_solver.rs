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
    std::time::Instant,
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
    //let contexts = get_token_contexts(&orders, pool);

    // Try to solve optimization problem
    //let solution = optimize_orders(&orders, &contexts)?;
    let (solution, p_vars, v_vars, z_vars) = optimize_orders(&orders)?;
    // Create a settlement from the solution

    // Extract and interpret the normalized prices
    let settlement = settle_valid_solution(&orders, pool, solution, &z_vars, &v_vars).ok()?;

    // Check if the constructed solution respects limit prices
    if is_valid_solution(&settlement) {
        Some(settlement)
    } else {
        None
    }
}

fn settle_valid_solution(
    orders: &[LimitOrder],
    pool: &ConstantProductOrder,
    solution: MicroLpSolution,
    z: &[Variable],
    v: &[Variable],
) -> Result<Settlement> {
    let mut executed_orders = Vec::new();
    //let mut non_executed_orders = Vec::new();

    // Here we directly use the `z` variables to determine which orders were executed
    for (order_i, order) in orders.iter().enumerate() {
        let z_val = solution.value(z[order_i]);
        let p_val = solution.value(v[order_i]);
        if z_val * p_val > 0.5 {
            executed_orders.push(order.clone());
            //} else {
            //    non_executed_orders.push(order.clone());
        }
    }

    let executed_token_context = get_token_contexts(&executed_orders, pool);
    assert_eq!(
        executed_token_context.len(),
        2,
        "Orders contain more than two tokens"
    );
    // Only need to switch addresses of the tokencontext
    let mut settlement = Settlement::new(
        executed_token_context
            .iter()
            .map(|ctx| (ctx.address, ctx.reserve))
            .collect(),
    );
    // Add executed orders directly to the main settlement
    for order in &executed_orders {
        let execution = LimitOrderExecution {
            filled: order.full_execution_amount(),
            fee: order.user_fee,
        };
        settlement.with_liquidity(order, execution)?;
    }
    return Ok(settlement);
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

#[cfg(test)]
mod tests {
    use {
        super::*,
        crate::liquidity::slippage::SlippageCalculator,
        ethcontract::H160,
        liquidity::tests::CapturingSettlementHandler,
        maplit::hashmap,
        model::{
            order::{Order, OrderData},
            TokenPair,
        },
        num::rational::Ratio,
        once_cell::sync::OnceCell,
        shared::{
            baseline_solver::BaselineSolvable, external_prices::ExternalPrices,
            sources::uniswap_v2::pool_fetching::Pool,
        },
    };

    fn to_wei(base: u128) -> U256 {
        U256::from(base) * U256::from(10).pow(18.into())
    }

    fn without_slippage() -> SlippageContext<'static> {
        static CONTEXT: OnceCell<(ExternalPrices, SlippageCalculator)> = OnceCell::new();
        let (prices, calculator) =
            CONTEXT.get_or_init(|| (Default::default(), SlippageCalculator::from_bps(0, None)));
        calculator.context(prices)
    }

    #[test]
    fn test_milp_solver_with_basic_orders() {
        let token_a = Address::from_low_u64_be(0);
        let token_b = Address::from_low_u64_be(1);
        let orders = vec![
            LimitOrder {
                sell_token: token_a,
                buy_token: token_b,
                sell_amount: to_wei(50),
                buy_amount: to_wei(45),
                kind: OrderKind::Sell,
                id: 0.into(),
                ..Default::default()
            },
            LimitOrder {
                sell_token: token_b,
                buy_token: token_a,
                sell_amount: to_wei(80),
                buy_amount: to_wei(100),
                kind: OrderKind::Buy,
                id: 1.into(),
                ..Default::default()
            },
        ];

        let pool = ConstantProductOrder {
            address: H160::from_low_u64_be(1),
            tokens: TokenPair::new(token_a, token_b).unwrap(),
            reserves: (to_wei(1000).as_u128(), to_wei(1000).as_u128()),
            fee: Ratio::new(3, 1000),
            settlement_handling: CapturingSettlementHandler::arc(),
        };

        let result = solve(&without_slippage(), orders.clone(), &pool).unwrap();

        // Check if the solution is valid
        assert!(is_valid_solution(&result));

        // Check if the clearing prices are set correctly
        let price_a = result.clearing_price(token_a).unwrap();
        let price_b = result.clearing_price(token_b).unwrap();
        assert!(price_a > U256::zero());
        assert!(price_b > U256::zero());
    }

    #[test]
    fn test_milp_solver_with_no_overlap() {
        let token_a = Address::from_low_u64_be(0);
        let token_b = Address::from_low_u64_be(1);
        let orders = vec![
            LimitOrder {
                sell_token: token_a,
                buy_token: token_b,
                sell_amount: to_wei(100),
                buy_amount: to_wei(150),
                kind: OrderKind::Sell,
                id: 0.into(),
                ..Default::default()
            },
            LimitOrder {
                sell_token: token_b,
                buy_token: token_a,
                sell_amount: to_wei(100),
                buy_amount: to_wei(150),
                kind: OrderKind::Sell,
                id: 1.into(),
                ..Default::default()
            },
        ];

        let pool = ConstantProductOrder {
            address: H160::from_low_u64_be(1),
            tokens: TokenPair::new(token_a, token_b).unwrap(),
            reserves: (to_wei(1000).as_u128(), to_wei(1000).as_u128()),
            fee: Ratio::new(3, 1000),
            settlement_handling: CapturingSettlementHandler::arc(),
        };

        let start = Instant::now();
        let slippage = SlippageContext::default();
        let result = solve(&slippage, orders, &pool).unwrap();
        let duration = start.elapsed();
        assert!(is_valid_solution(&result));
        println!(
            "Test 'test_milp_solver_with_basic_orders' took: {:?}",
            duration
        );
    }

    #[test]
    fn test_milp_solver_with_overhang() {
        let token_a = Address::from_low_u64_be(0);
        let token_b = Address::from_low_u64_be(1);
        let orders = vec![
            LimitOrder {
                sell_token: token_a,
                buy_token: token_b,
                sell_amount: to_wei(150),
                buy_amount: to_wei(100),
                kind: OrderKind::Sell,
                id: 0.into(),
                ..Default::default()
            },
            LimitOrder {
                sell_token: token_b,
                buy_token: token_a,
                sell_amount: to_wei(100),
                buy_amount: to_wei(150),
                kind: OrderKind::Sell,
                id: 1.into(),
                ..Default::default()
            },
            LimitOrder {
                sell_token: token_b,
                buy_token: token_a,
                sell_amount: to_wei(100),
                buy_amount: to_wei(150),
                kind: OrderKind::Sell,
                id: 1.into(),
                ..Default::default()
            },
        ];

        let pool = ConstantProductOrder {
            address: H160::from_low_u64_be(1),
            tokens: TokenPair::new(token_a, token_b).unwrap(),
            reserves: (to_wei(1000).as_u128(), to_wei(1000).as_u128()),
            fee: Ratio::new(3, 1000),
            settlement_handling: CapturingSettlementHandler::arc(),
        };

        let slippage = SlippageContext::default();
        let result = solve(&slippage, orders, &pool).unwrap();

        // Check if the solution is valid
        assert!(is_valid_solution(&result));
    }
}
