use {
    crate::{
        liquidity::{self, slippage::SlippageContext, LimitOrderExecution},
        settlement::{PricedTrade, Settlement},
    },
    anyhow::Result,
    liquidity::{AmmOrderExecution, ConstantProductOrder, LimitOrder},
    model::order::OrderKind,
    num::{rational::Ratio, BigInt, BigRational, CheckedDiv},
    number::conversions::{big_int_to_u256, big_rational_to_u256, u256_to_big_int},
    primitive_types::U256, H160,
    shared::{
        conversions::{RatioExt, U256Ext},
        http_solver::model::TokenAmount,
    },
    std::collections::HashMap,HashSet,
    web3::types::Address,
    good_lp::{variables, variable, Problem, Expression, SolverModel, Solution},
};


#[derive(Debug, Clone)]
struct TokenContext {
    address: H160,
    reserve: U256,
    buy_volume: U256,
    sell_volume: U256,
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


/// Detect if there are cycles in the orders
pub fn detect_cycle(orders: &[LimitOrder]) -> bool {
    // Build adjacency list
    let mut graph: HashMap<H160, Vec<H160>> = HashMap::new();
    for order in orders {
        graph
            .entry(order.sell_token)
            .or_default()
            .push(order.buy_token);
    }

    // Set to track visited nodes
    let mut visited = HashSet::new();
    // Set to track nodes in the current recursion stack
    let mut recursion_stack = HashSet::new();

    // Helper function for depth-first search (DFS)
    fn dfs(
        node: H160,
        graph: &HashMap<H160, Vec<H160>>,
        visited: &mut HashSet<H160>,
        recursion_stack: &mut HashSet<H160>,
    ) -> bool {
        if !visited.insert(node) {
            return false;
        }
        recursion_stack.insert(node);

        if let Some(neighbors) = graph.get(&node) {
            for &neighbor in neighbors {
                if recursion_stack.contains(&neighbor) || dfs(neighbor, graph, visited, recursion_stack) {
                    return true;
                }
            }
        }

        recursion_stack.remove(&node);
        false
    }

    // Run DFS for each node in the graph
    for &node in graph.keys() {
        if !visited.contains(&node) && dfs(node, &graph, &mut visited, &mut recursion_stack) {
            return true; // Cycle detected
        }
    }

    false
}


fn solve_orders(
    slippage: &SlippageContext,
    orders: &[LimitOrder],
    pool: &ConstantProductOrder,
    context_s: &TokenContext,
) -> Option<Settlement> {
    if context_s.detect_cycle(orders, context_a, context_b).ok(){

    }else if context_a.is_excess_after_fees(context_b, pool.fee) {
        solve_with_uniswap(slippage, orders, pool, context_b, context_a)
    } else if context_b.is_excess_after_fees(context_a, pool.fee) {
        solve_with_uniswap(slippage, orders, pool, context_a, context_b)
    } else {
        solve_without_uniswap
    }
}



pub fn solve(
    slippage: &SlippageContext,
    orders: impl IntoIterator<Item = LimitOrder>,
    pool: &ConstantProductOrder,
) -> Option<Settlement> {
    let mut orders: Vec<LimitOrder> = orders.into_iter().collect();
    while !orders.is_empty() {
        let context_s = split_into_contexts(&orders, pool);
        if let Some(valid_solution) =
            solve_orders(slippage, &orders, pool, &context_s).filter(is_valid_solution)
        {
            return Some(valid_solution);
        } else {
            // remove order with worst limit price that is selling excess token (to make it
            // less excessive) and try again
            let excess_token = if context_a.is_excess_before_fees(&context_b) {
                context_a.address
            } else {
                context_b.address
            };
            let order_to_remove = orders
                .iter()
                .enumerate()
                .filter(|o| o.1.sell_token == excess_token)
                .max_by(|lhs, rhs| {
                    (lhs.1.buy_amount * rhs.1.sell_amount)
                        .cmp(&(lhs.1.sell_amount * rhs.1.buy_amount))
                });
            match order_to_remove {
                Some((index, _)) => orders.swap_remove(index),
                None => break,
            };
        }
    }

    None
}







fn split_into_contexts(
    orders: &[LimitOrder],
    pool: &ConstantProductOrder,
) -> HashMap<H160, TokenContext> {
    let mut contexts = HashMap::new();
    for order in orders {
        let buy_context = contexts
            .entry(order.buy_token)
            .or_insert_with(|| TokenContext {
                address: order.buy_token,
                reserve: pool
                    .get_reserve(&order.buy_token)
                    .unwrap_or_else(|| panic!("No reserve for token {}", &order.buy_token)),
                buy_volume: U256::zero(),
                sell_volume: U256::zero(),
            });
        if matches!(order.kind, OrderKind::Buy) {
            buy_context.buy_volume += order.buy_amount
        }

        let sell_context = contexts
            .entry(order.sell_token)
            .or_insert_with(|| TokenContext {
                address: order.sell_token,
                reserve: pool
                    .get_reserve(&order.sell_token)
                    .unwrap_or_else(|| panic!("No reserve for token {}", &order.sell_token)),
                buy_volume: U256::zero(),
                sell_volume: U256::zero(),
            });
        if matches!(order.kind, OrderKind::Sell) {
            sell_context.sell_volume += order.sell_amount
        }
    }
    contexts
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
            baseline_solver::BaselineSolvable,
            external_prices::ExternalPrices,
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
    fn finds_clearing_using_ring() {
        let token_a = Address::from_low_u64_be(0);
        let token_b = Address::from_low_u64_be(1);
        let orders = vec![
            LimitOrder {
                sell_token: token_a,
                buy_token: token_b,
                sell_amount: to_wei(1001),
                buy_amount: to_wei(1000),
                kind: OrderKind::Sell,
                id: 0.into(),
                ..Default::default()
            },
            LimitOrder {
                sell_token: token_b,
                buy_token: token_a,
                sell_amount: to_wei(1001),
                buy_amount: to_wei(1000),
                kind: OrderKind::Sell,
                id: 1.into(),
                ..Default::default()
            },
            LimitOrder {
                sell_token: tokens_c,
                buy_token: tokens_d,
                sell_amount: U256::from(80),
                buy_amount: U256::from(70),
                kind: OrderKind::Sell,
                id: 1.into(),
                ..Default::default()
            },
            LimitOrder {
                sell_token: tokens_d,
                buy_token: tokens_a,
                sell_amount: U256::from(70),
                buy_amount: U256::from(60),
                kind: OrderKind::Sell,
                id: 1.into(),
                ..Default::default()
            },
        ];

        let amm_handler = CapturingSettlementHandler::arc();
        let pool = ConstantProductOrder {
            address: H160::from_low_u64_be(1),
            tokens: TokenPair::new(token_a, token_b).unwrap(),
            reserves: (to_wei(1_000_001).as_u128(), to_wei(1_000_000).as_u128()),
            fee: Ratio::new(3, 1000),
            settlement_handling: amm_handler.clone(),
        };
        let result = solve(&SlippageContext::default(), orders, &pool).unwrap();
        assert!(amm_handler.calls().is_empty());
        assert_eq!(
            result.clearing_prices(),
            &maplit::hashmap! {
                token_a => to_wei(1_000_000),
                token_b => to_wei(1_000_001)
            }
        );
    }
}

