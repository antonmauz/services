// Heuristic
//
// Solve(Slippage, orders, pool)
// - Starting point of the solution
// - receives from solvers::boundary::\*
//  
//
// fn create_context()
// Creates a list/hashmap of tokencontexts
// - adress
// - reserve
// - buy volume
// - sell volumne
//
//
// fn solving_balanced_trades()
// - creates context
// - uses optimizer to build a basket of directly swappable trades under constraint of tokenprice
// - finds balanced tokencontexts
// - Swaps balanced trades -> pushes to solution
// - returns list of not swappable trades (excess orders)
//  
//
// fn creates_graph()
// - Graph over excess orders
// - A -- B
// | |
// D -- C -- E - F
// \ /
// G
//
// fn find_cycles()
// - Finds the cycles which maximises trading volumne
// - Constraint:
// - Limit price
// - Volumne
//
// fn pass_leftovers()
// - passes unsettled trades to the baseline trader
