pub mod driver;
pub mod encoding;
pub mod gas_price_estimation;
pub mod http_solver;
pub mod interactions;
pub mod liquidity;
pub mod naive_solver;
pub mod orderbook;
pub mod settlement;
pub mod settlement_submission;
pub mod solver;
pub mod uniswap;

use anyhow::Result;
use ethcontract::{contract::MethodDefaults, Account, Http, PrivateKey, Web3};

pub async fn get_settlement_contract(
    web3: &Web3<Http>,
    chain_id: u64,
    key: PrivateKey,
) -> Result<contracts::GPv2Settlement> {
    let mut settlement_contract = contracts::GPv2Settlement::deployed(&web3).await?;
    *settlement_contract.defaults_mut() = MethodDefaults {
        from: Some(Account::Offline(key, Some(chain_id))),
        ..Default::default()
    };
    Ok(settlement_contract)
}
