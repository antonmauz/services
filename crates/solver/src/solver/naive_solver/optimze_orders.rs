use {
    crate::{
        liquidity::{
            self, slippage::SlippageContext, AmmOrderExecution, ConstantProductOrder, LimitOrder,
            LimitOrderExecution,
        },
        settlement::{PricedTrade, Settlement},
    },
    good_lp::*,
    model::order::OrderKind,
    primitive_types::{H160, U256},
    solvers::microlp::MicroLpSolution,
    web3::types::Address,
};

// Internal struct for the MIP model
struct OrderData {
    j: usize, // token index to buy
    k: usize, // token index to sell
    bar_x: f64,
    bar_y: f64,
    pi: f64,
}

struct TokenContext {
    address: Address,
    //reserve: U256,
    //buy_volume: U256,
    //sell_volume: U256,
}

// Convert U256 to f64 carefully (watch out for overflow in real scenarios)
fn u256_to_f64(val: U256) -> f64 {
    val.as_u128() as f64
}

fn u256_wei_to_f64_eth(val: U256) -> f64 {
    // Divide by 1e18 before converting
    let eth_scale = 1e18;
    let lower_part = val.low_u128() as f64; // Only accurate if val fits in 128 bits
    lower_part / eth_scale
}

fn print_variable_names_and_values(solution: &MicroLpSolution, variables: &[Variable]) {
    for (i, var) in variables.iter().enumerate() {
        let value = solution.value(*var);
        println!("Variable {}: Value = {}", i, value);
    }
}

pub fn optimize_orders(
    order_a: &[LimitOrder],
    order_b: &[LimitOrder],
    context_a: &TokenContext,
    context_b: &TokenContext,
) -> Option<MicroLpSolution> {
    // Combine all orders into a single vector for the model
    let all_orders: Vec<&LimitOrder> = order_a.iter().chain(order_b.iter()).collect();

    fn token_index(address: H160, a: &TokenContext, b: &TokenContext) -> Option<usize> {
        if address == a.address {
            Some(0)
        } else if address == b.address {
            Some(1)
        } else {
            None
        }
    }

    // Map each LimitOrder to OrderData for the MIP model
    let mut orders_data = Vec::new();

    for order in &all_orders {
        let sell_token_idx = token_index(order.sell_token, context_a, context_b).unwrap_or(0);
        let buy_token_idx = token_index(order.buy_token, context_a, context_b).unwrap_or(0);

        let sell_amount_f = u256_wei_to_f64_eth(order.sell_amount);
        let buy_amount_f = u256_wei_to_f64_eth(order.buy_amount);

        // bar_x: max buy of token j
        // bar_y: max sell of token k
        // pi = p_{j|k} limit price = buy_amount / sell_amount
        let pi = buy_amount_f / sell_amount_f;
        let bar_x = buy_amount_f;
        let bar_y = sell_amount_f;

        orders_data.push(OrderData {
            j: buy_token_idx,
            k: sell_token_idx,
            bar_x,
            bar_y,
            pi,
        });
    }

    let n_o = orders_data.len();
    let n_t = 2; // We have only two tokens: context_a and context_b

    // Define token parameters (adjust as needed)
    // underline_p, bar_p, gamma are model parameters
    struct TokenData {
        underline_p: f64,
        bar_p: f64,
        gamma: f64,
    }
    let tokens = vec![
        TokenData {
            underline_p: 0.1,
            bar_p: 10.0,
            gamma: 0.5,
        },
        TokenData {
            underline_p: 0.1,
            bar_p: 10.0,
            gamma: 0.5,
        },
    ];

    // Big-M constants and epsilon
    //let big_m_1 = 1_000_000.0;
    //let big_m_2 = 1_000_000.0;
    let epsilon = 0.001;

    let mut problem_vars = ProblemVariables::new();

    // Define the variables using add_vector
    let p: Vec<Variable> = problem_vars.add_vector(variable().min(0.0).name("p[]"), n_t);
    let v: Vec<Variable> = problem_vars.add_vector(variable().min(0.0).name("v[]"), n_o);
    let z: Vec<Variable> = problem_vars.add_vector(variable().binary().name("z[]"), n_o);

    // Now create the model with an objective:
    /*
    let mut model = problem_vars
        .maximise(v.iter().cloned().sum::<Expression>())
        .using(default_solver);
    */
    let mut model = problem_vars
        .maximise(v.iter().cloned().sum::<Expression>())
        .using(default_solver);

    // After creating the model, add constraints for p[j] bounds based on tokens[j].

    // After creating the model, set bounds for p[j] based on tokens[j]

    for j in 0..n_t {
        model = model.with(constraint!(p[j] >= tokens[j].underline_p));
        model = model.with(constraint!(p[j] <= tokens[j].bar_p));
    }

    // Price normalization constraint: sum_j gamma_j p_j = 1
    let normalization_expr =
        (0..n_t).fold(Expression::from(0.0), |acc, j| acc + tokens[j].gamma * p[j]);
    model = model.with(normalization_expr.eq(1.0));

    // Token balance constraints:
    // For each order that buys token j and sells token k:
    //   t_b[i][j] = 1, t_s[i][j] = 1 for the respective tokens
    let mut t_b = vec![vec![0.0; n_t]; n_o];
    let mut t_s = vec![vec![0.0; n_t]; n_o];

    for (i, od) in orders_data.iter().enumerate() {
        t_b[i][od.j] = 1.0;
        t_s[i][od.k] = 1.0;
    }

    // For each token j: sum_i t_b[i,j]*v[i] = sum_i t_s[i,j]*v[i]
    for jj in 0..n_t {
        let bought_expr = (0..n_o).fold(Expression::from(0.0), |acc, i| acc + t_b[i][jj] * v[i]);
        let sold_expr = (0..n_o).fold(Expression::from(0.0), |acc, i| acc + t_s[i][jj] * v[i]);
        model = model.with(bought_expr.eq(sold_expr));
    }

    // Big-M style constraints (14a-f):
    // Instead of using a fixed big_m_1 or big_m_2, we reuse logic from original code:
    // Adjust if needed.
    for i in 0..n_o {
        let od = &orders_data[i];
        let j = od.j;
        let k = od.k;
        let pi = od.pi;
        let bar_x_i = od.bar_x;
        let bar_y_i = od.bar_y;

        // (14a)
        model = model.with(constraint!(
            p[j] <= pi * p[k] + (1.0 - z[i]) * (tokens[j].bar_p - pi * tokens[k].underline_p)
        ));

        // (14b)
        model = model.with(constraint!(
            p[j] >= (pi + epsilon) * p[k]
                + z[i] * (tokens[j].underline_p - (pi + epsilon) * tokens[k].bar_p)
        ));

        // (14c)
        if bar_x_i.is_finite() {
            model = model.with(constraint!(v[i] <= bar_x_i * p[j]));
        }

        // (14d)
        if bar_x_i.is_finite() {
            model = model.with(constraint!(v[i] <= bar_x_i * tokens[j].bar_p * z[i]));
        }

        // (14e)
        model = model.with(constraint!(v[i] <= bar_y_i * p[k]));

        // (14f)
        if bar_y_i.is_finite() {
            model = model.with(constraint!(v[i] <= bar_y_i * tokens[k].bar_p * z[i]));
        }
    }
    //model = add_additional_inequalities(model, &orders_data, &p, &z);
    // Solve the model
    let solution = model.solve().ok();

    /*
    let solution1: Option<MicroLpSolution> = solution;

    //let solution_variables: Vec<_> = variables!.iter().map(|&v| Some(solution).value(v)).collect();

    if solution.is_some() {
        let solution = solution.unwrap();
        for (i, &var) in p.iter().enumerate() {
            println!("Variable p[{}]: {}", i, solution.value(var));
        }
        for (i, &var) in v.iter().enumerate() {
            println!("Variable v[{}]: {}", i, solution.value(var));
        }
        for (i, &var) in z.iter().enumerate() {
            println!("Variable z[{}]: {}", i, solution.value(var));
        }
    } else {
        println!("Error")
    } */
    // Call this function at the end of your `optimize_orders` function
    if let Some(solution) = solution.as_ref() {
        println!("---------- RESULTS ----------\n");
        println!("Prices: \n");
        print_variable_names_and_values(&solution, &p);
        println!("-----------------------\n");
        println!("Volumne in reference Token: \n");
        print_variable_names_and_values(&solution, &v);
        println!("-----------------------\n");
        println!("Order executed or not: \n");
        print_variable_names_and_values(&solution, &z);
        println!("Order executed or not:\n ");
    }

    solution
}
/*
fn add_additional_inequalities(
    mut model: impl SolverModel,
    orders_data: &Vec<OrderData>,
    p: &Vec<Variable>,
    z: &Vec<Variable>,
) -> impl SolverModel {
    // ============= INEQUALITIES (17) ==============
    // Group orders by token pair (j,k)
    let mut orders_by_pair: HashMap<(usize, usize), Vec<(usize, f64)>> = HashMap::new();
    for (i, od) in orders_data.iter().enumerate() {
        orders_by_pair
            .entry((od.j, od.k))
            .or_default()
            .push((i, od.pi));
    }

    // Sort each group by pi and add chain inequalities
    for ((j, k), orders_vec) in &mut orders_by_pair {
        orders_vec.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());
        for idx in 0..(orders_vec.len() - 1) {
            let (i1, pi1) = orders_vec[idx];
            let (i2, pi2) = orders_vec[idx + 1];
            // z[i1] ≤ z[i2]
            model = model.with(constraint!(z[i1]<=(z[i2])));

            // If pi1 == pi2, then z[i1] = z[i2]
            if (pi1 - pi2).abs() < 1e-12 {
                model = model.with(constraint!(z[i1]==(z[i2])));
            }
        }
    }

    // ============= OPPOSITE DIRECTIONS (m=2 CYCLES) (18) and (19) ==============
    // For each pair (j,k), if (k,j) exists, check pairs of orders
    let mut orders_by_pair_map: HashMap<(usize, usize), Vec<(usize, f64)>> = HashMap::new();
    for (i, od) in orders_data.iter().enumerate() {
        orders_by_pair_map
            .entry((od.j, od.k))
            .or_default()
            .push((i, od.pi));
    }

    for ((j, k), vec_jk) in &orders_by_pair_map {
        if let Some(vec_kj) = orders_by_pair_map.get(&(k.clone(), j.clone())) {
            // For each ω1 in (j,k) and ω2 in (k,j):
            for &(i1, pi1) in vec_jk {
                for &(i2, pi2) in vec_kj {
                    let product = pi1 * pi2;
                    // If pi1 * pi2 < 1 => z[i1] + z[i2] ≤ 1
                    // If pi1 * pi2 ≥ 1 => z[i1] + z[i2] ≥ 1
                    let expr = z[i1] + z[i2];
                    if product < 1.0 {
                        model = model.with(expr.leq(1.0));
                    } else {
                        model = model.with(expr.geq(1.0));
                    }
                }
            }
        }
    }

    // ============= CYCLES OF LENGTH 3 (as an example) ==============
    // For all triples of distinct tokens (j1,j2,j3), if orders form j1->j2, j2->j3, j3->j1 cycle,
    // add constraints:
    // If ∏ pi_i < 1 => ∑ z_i ≤ m - 1 (m=3 => ≤ 2)
    // If ∏ pi_i ≥ 1 => ∑ z_i ≥ 1
    //
    // We'll map (j,k) to orders and try to find such triples.
    let mut order_map: HashMap<(usize, usize), Vec<(usize, f64)>> = HashMap::new();
    let tokens_used: Vec<usize> = orders_data.iter().flat_map(|o| vec![o.j, o.k]).collect();
    let unique_tokens: Vec<usize> = {
        let mut set = std::collections::HashSet::new();
        tokens_used.into_iter().filter(|x| set.insert(*x)).collect()
    };

    for (i, od) in orders_data.iter().enumerate() {
        order_map.entry((od.j, od.k)).or_default().push((i, od.pi));
    }

    fn add_cycle_constraints(
        mut model: impl SolverModel,
        z: &Vec<Variable>,
        cycle_orders: &[(usize, f64)],
    ) -> impl SolverModel {
        let m = cycle_orders.len();
        let product_pi: f64 = cycle_orders.iter().map(|(_, pi)| pi).product();
        let sum_z_expr = cycle_orders
            .iter()
            .fold(Expression::from(0.0), |acc, (i, _)| acc + z[*i]);

        if product_pi < 1.0 {
            // sum z_i ≤ m - 1
            model = model.with(sum_z_expr.leq((m as f64) - 1.0));
        } else {
            // sum z_i ≥ 1
            model = model.with(sum_z_expr.geq(1.0));
        }

        model
    }
}
 */
#[cfg(test)]
mod tests {
    use super::*;
    use primitive_types::U256;
    use web3::types::H160;

    fn to_wei(base: u128) -> U256 {
        U256::from(base) * U256::from(10).pow(18.into())
    }

    #[test]
    fn test_optimize_orders_full_execution() {
        let orders_a = vec![
            LimitOrder {
                id: 1.into(),
                sell_token: H160::from_low_u64_be(0),
                buy_token: H160::from_low_u64_be(1),
                sell_amount: to_wei(100),
                buy_amount: to_wei(90),
                kind: OrderKind::Sell,
                ..Default::default()
            },
            LimitOrder {
                id: 3.into(),
                sell_token: H160::from_low_u64_be(0),
                buy_token: H160::from_low_u64_be(1),
                sell_amount: to_wei(200),
                buy_amount: to_wei(180),
                kind: OrderKind::Sell,
                ..Default::default()
            },
            LimitOrder {
                id: 5.into(),
                sell_token: H160::from_low_u64_be(0),
                buy_token: H160::from_low_u64_be(1),
                sell_amount: to_wei(400),
                buy_amount: to_wei(390),
                kind: OrderKind::Sell,
                ..Default::default()
            },
        ];

        let orders_b = vec![
            LimitOrder {
                id: 2.into(),
                sell_token: H160::from_low_u64_be(1),
                buy_token: H160::from_low_u64_be(0),
                sell_amount: to_wei(90),
                buy_amount: to_wei(100),
                kind: OrderKind::Sell,
                ..Default::default()
            },
            LimitOrder {
                id: 4.into(),
                sell_token: H160::from_low_u64_be(1),
                buy_token: H160::from_low_u64_be(0),
                sell_amount: to_wei(160),
                buy_amount: to_wei(300),
                kind: OrderKind::Sell,
                ..Default::default()
            },
        ];

        let context_a = TokenContext {
            address: H160::from_low_u64_be(0),
            //reserve: to_wei(1000),
            //buy_volume: to_wei(280),
            //sell_volume: to_wei(300),
        };

        let context_b = TokenContext {
            address: H160::from_low_u64_be(1),
            //reserve: to_wei(1000),
            //buy_volume: to_wei(300),
            //sell_volume: to_wei(280),
        };

        let solution = optimize_orders(&orders_a, &orders_b, &context_a, &context_b);
        assert!(solution.is_some(), "solution found")
    }
}
