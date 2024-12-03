use {
    crate::{
        liquidity::{
            self, slippage::SlippageContext, AmmOrderExecution, ConstantProductOrder, LimitOrder,
            LimitOrderExecution,
        },
        settlement::{PricedTrade, Settlement},
    },
    anyhow::Result,
    ethcontract::H160,
    model::order::OrderKind,
    num::{rational::Ratio, BigInt, BigRational, CheckedDiv},
    number::conversions::{big_int_to_u256, big_rational_to_u256, u256_to_big_int},
    petgraph::algo::tarjan_scc,
    petgraph::dot::{Config, Dot},
    petgraph::graph::{DiGraph, NodeIndex},
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

impl TokenContext {
    pub fn can_trade(&self, required_amount: U256) -> bool {
        self.reserve >= required_amount
    }
}

/// Adapts the solve function to find cycles
pub fn solve(
    slippage: &SlippageContext,
    orders: impl IntoIterator<Item = LimitOrder>,
    pool: &ConstantProductOrder,
) {
    let orders: Vec<LimitOrder> = orders.into_iter().collect();
    // Transform LimitOrder into tuples
    let order_tuples: Vec<(H160, H160, U256)> = orders
        .iter()
        .map(|order| {
            (
                order.sell_token,
                order.buy_token,
                order.sell_amount, // or order.buy_amount, depending on your needs
            )
        })
        .collect();
    let token_graph = build_graph(&order_tuples);
    let cycles = find_cycles(&token_graph);

    // Log or assert to test the functions
}

/// Build a graph representation of token pairs from orders
fn build_graph(orders: &[(H160, H160, U256)]) -> DiGraph<H160, U256> {
    let mut graph = DiGraph::new();
    let mut node_indices = HashMap::new();

    for &(sell_token, buy_token, amount) in orders {
        let sell_index = *node_indices
            .entry(sell_token)
            .or_insert_with(|| graph.add_node(sell_token));
        let buy_index = *node_indices
            .entry(buy_token)
            .or_insert_with(|| graph.add_node(buy_token));
        graph.add_edge(sell_index, buy_index, amount);
    }
    graph
}

fn find_cycles(graph: &DiGraph<H160, U256>) -> Vec<Vec<H160>> {
    let sccs = tarjan_scc(graph);
    sccs.into_iter()
        .filter(|scc| scc.len() > 1) // Filter out single-node SCCs
        .map(|scc| scc.into_iter().map(|index| graph[index]).collect())
        .collect()
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
                    .get_reserves(&order.buy_token)
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
                    .get_reserves(&order.sell_token)
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
    fn finds_clearing_price_with_sell_orders_on_both_sides() {
        let token_a = Address::from_low_u64_be(0);
        let token_b = Address::from_low_u64_be(1);
        let token_c = Address::from_low_u64_be(2);
        let orders = vec![
            LimitOrder {
                sell_token: token_a,
                buy_token: token_b,
                sell_amount: to_wei(40),
                buy_amount: to_wei(30),
                kind: OrderKind::Sell,
                id: 0.into(),
                ..Default::default()
            },
            LimitOrder {
                sell_token: token_b,
                buy_token: token_c,
                sell_amount: to_wei(30),
                buy_amount: to_wei(20),
                kind: OrderKind::Sell,
                id: 1.into(),
                ..Default::default()
            },
            LimitOrder {
                sell_token: token_c,
                buy_token: token_a,
                sell_amount: to_wei(20),
                buy_amount: to_wei(40),
                kind: OrderKind::Sell,
                id: 2.into(),
                ..Default::default()
            },
        ];

        let amm_handler = CapturingSettlementHandler::arc();
        let pool = ConstantProductOrder {
            address: H160::from_low_u64_be(1),
            tokens: TokenPair::new(token_a, token_b).unwrap(),
            reserves: (to_wei(1000).as_u128(), to_wei(1000).as_u128()),
            fee: Ratio::new(3, 1000),
            settlement_handling: amm_handler.clone(),
        };

        let orders: Vec<LimitOrder> = orders.into_iter().collect();
        let order_tuples: Vec<(H160, H160, U256)> = orders
            .iter()
            .map(|order| {
                (
                    order.sell_token,
                    order.buy_token,
                    order.sell_amount, // or order.buy_amount, depending on your needs
                )
            })
            .collect();
        let token_graph = build_graph(&order_tuples);
        solve(&without_slippage(), orders.clone(), &pool);
        println!(
            "{:?}",
            Dot::with_config(&token_graph, &[Config::EdgeNoLabel])
        );
        // Make sure the uniswap interaction is using the correct direction
        let interaction = amm_handler.calls()[0].clone();
        assert_eq!(interaction.input_max.token, token_b);
        assert_eq!(interaction.output.token, token_a);

        // Make sure the sell amounts +/- uniswap interaction satisfy min_buy amounts
        assert!(orders[0].sell_amount + interaction.output.amount >= orders[1].buy_amount);
        assert!(orders[1].sell_amount - interaction.input_max.amount > orders[0].buy_amount);

        // Make sure the sell amounts +/- uniswap interaction satisfy expected buy
        // amounts given clearing price

        // Multiplying sellAmount with priceA, gives us sell value in "$", divided by
        // priceB gives us value in buy token We should have at least as much to
        // give (sell amount +/- uniswap) as is expected by the buyer
        //let expected_buy = (orders[0].sell_amount * price_a).ceil_div(&price_b);
        //assert!(orders[1].sell_amount - interaction.input_max.amount >= expected_buy);

        //let expected_buy = (orders[1].sell_amount * price_b).ceil_div(&price_a);
        //assert!(orders[0].sell_amount + interaction.input_max.amount >= expected_buy);
    }
}
