use circom_algebra::algebra::{Constraint};
use std::collections::{HashSet, LinkedList};
use super::{ConstraintStorage};
use super::preprocess_non_linear::*;
use circom_algebra::num_bigint::BigInt;
use std::sync::Arc;


pub struct NonLinearClustersConfig {
    pub field: BigInt,
    pub storage: ConstraintStorage,
}


pub fn obtain_non_linear_clusters(config: NonLinearClustersConfig) -> LinkedList<ConstraintStorage>{
    let mut processed_constraints = ProcessedConstraints::new(&config.storage);
    processed_constraints.compute_zero_constraints(&config.storage, &config.field);
    processed_constraints.compute_clusters_constraints(&config.storage);
    processed_constraints.clusters
}


pub struct NonLinearConfig {
    pub field: BigInt,
    pub storage: ConstraintStorage,
    pub forbidden: Arc<HashSet<usize>>,
}

pub fn deduce_linear_constraints(config: NonLinearConfig)
 -> (LinkedList<Constraint<usize>>, LinkedList<Vec<usize>>)
{

    let config = crate::non_linear_simplification::NonLinearConfig {
        field: config.field,
        storage: config.storage,
        forbidden: Arc::clone(&config.forbidden),
    };

    crate::cluster_non_linear::obtain_linear_constraints(config)
}



