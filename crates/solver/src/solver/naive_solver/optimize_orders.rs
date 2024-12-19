use {
    crate::liquidity::LimitOrder,
    good_lp::*,
    model::order::OrderKind,
    primitive_types::{H160, U256},
    solvers::microlp::MicroLpSolution,
    std::collections::{HashMap, HashSet},
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
    reserve: U256,
    buy_volume: U256,
    sell_volume: U256,
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

// Function to collect unique tokens and assign indices
fn collect_unique_tokens(all_orders: &[LimitOrder]) -> HashMap<H160, usize> {
    let mut tokens = HashSet::new();

    for order in all_orders {
        tokens.insert(order.sell_token);
        tokens.insert(order.buy_token);
    }

    let mut token_to_index = HashMap::new();
    for (i, token) in tokens.into_iter().enumerate() {
        token_to_index.insert(token, i);
    }

    token_to_index
}

pub fn optimize_orders(
    all_orders: &[LimitOrder],
    //_contexts: &[TokenContext],
) -> Option<(MicroLpSolution, Vec<Variable>, Vec<Variable>, Vec<Variable>)> {
    // Collect unique tokens and assign indices
    let token_to_index = collect_unique_tokens(all_orders);
    let n_t = token_to_index.len();

    // Map each LimitOrder to OrderData for the MIP model
    let mut orders_data = Vec::new();

    for order in all_orders.iter() {
        let sell_token_idx = *token_to_index.get(&order.sell_token).unwrap();
        let buy_token_idx = *token_to_index.get(&order.buy_token).unwrap();

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

    // Define token parameters (adjust as needed)
    struct TokenData {
        underline_p: f64,
        bar_p: f64,
        gamma: f64,
    }
    // underline_p, bar_p, gamma are model parameters
    let mut tokens = Vec::new();
    for (token, _) in &token_to_index {
        tokens.push(TokenData {
            underline_p: 0.5, // Example: adjust as needed
            bar_p: 10.0,      // Example: adjust based on context
            gamma: 0.5,       // Example: adjust as needed
        });
    }

    let epsilon = 0.001;

    let mut problem_vars = ProblemVariables::new();

    // Define the variables using add_vector
    let p: Vec<Variable> = problem_vars.add_vector(variable().min(0.0).name("p[]"), n_t);
    let v: Vec<Variable> = problem_vars.add_vector(variable().min(0.0).name("v[]"), n_o);
    let z: Vec<Variable> = problem_vars.add_vector(variable().binary().name("z[]"), n_o);

    // Now create the model with an objective:
    let mut model = problem_vars
        .maximise(v.iter().cloned().sum::<Expression>())
        .using(default_solver);

    // After creating the model, add constraints for p[j] bounds based on tokens[j].
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
        println!("\n ");
        println!("---------- RESULTS ----------\n ");
    }

    solution.map(|sol| (sol, p, v, z))
}

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
        let all_orders = vec![
            LimitOrder {
                id: 1.into(),
                sell_token: H160::from_low_u64_be(1),
                buy_token: H160::from_low_u64_be(2),
                sell_amount: to_wei(100),
                buy_amount: to_wei(90),
                kind: OrderKind::Sell,
                ..Default::default()
            },
            LimitOrder {
                id: 2.into(),
                sell_token: H160::from_low_u64_be(1),
                buy_token: H160::from_low_u64_be(2),
                sell_amount: to_wei(100),
                buy_amount: to_wei(90),
                kind: OrderKind::Sell,
                ..Default::default()
            },
            LimitOrder {
                id: 3.into(),
                sell_token: H160::from_low_u64_be(2),
                buy_token: H160::from_low_u64_be(1),
                sell_amount: to_wei(90),
                buy_amount: to_wei(100),
                kind: OrderKind::Sell,
                ..Default::default()
            },
            LimitOrder {
                id: 4.into(),
                sell_token: H160::from_low_u64_be(2),
                buy_token: H160::from_low_u64_be(1),
                sell_amount: to_wei(90),
                buy_amount: to_wei(100),
                kind: OrderKind::Sell,
                ..Default::default()
            },
            LimitOrder {
                id: 5.into(),
                sell_token: H160::from_low_u64_be(2),
                buy_token: H160::from_low_u64_be(1),
                sell_amount: to_wei(90),
                buy_amount: to_wei(100),
                kind: OrderKind::Sell,
                ..Default::default()
            },
        ];
        let solution = optimize_orders(&all_orders);
        assert!(solution.is_some(), "solution found")
    }
}
