use circom_algebra::constraint_storage::{ ConstraintID};
use std::collections::{HashMap, LinkedList};
use super::{ConstraintStorage,  Monomial};
use crate::clusters_utils::{Cluster, ClusterArena, ClusterPath};
use crate::BigInt;



pub struct ProcessedConstraints
{
    pub(crate) clusters: LinkedList<ConstraintStorage>,
    pub(crate) list_monomials: LinkedList<Monomial>,
    pub(crate) map_constraints_monomials: HashMap<ConstraintID, Vec<Monomial>>,
    pub(crate) map_monomials_constraints: HashMap<Monomial, Vec<ConstraintID>>,
    //pub(crate) map_monomials_constraints: HashMap<Monomial, HashSet<ConstraintID>>,

}
impl ProcessedConstraints{
    pub fn new(
        storage: &ConstraintStorage,
    ) -> ProcessedConstraints {
        let mut proc_cons = ProcessedConstraints{ 
            clusters: LinkedList::new(),
            list_monomials: LinkedList::new(),
            map_constraints_monomials: HashMap::new(), 
            map_monomials_constraints: HashMap::new(), 
        };
        proc_cons.create_table_monomials(storage);
        proc_cons
    }

    

    fn create_table_monomials(
        &mut self,
        storage: &ConstraintStorage, 
    ){

        for c_id in storage.get_ids() {
            let constraint = storage.read_constraint(c_id).unwrap();
            if !constraint.is_empty(){
                let mut monomials_cid = Vec::new();
                for monomial in constraint.take_possible_cloned_monomials() {
                    match self.map_monomials_constraints.get_mut(&monomial){
                        Some(map_mon) =>{
                         map_mon.push(c_id);
                        },
                        None =>{
                            let mut map_mon = Vec::new();
                            map_mon.push(c_id);
                            //let mut map_mon = HashSet::new();
                            //map_mon.insert(c_id);
                            self.map_monomials_constraints.insert(monomial, map_mon);
                            self.list_monomials.push_back(monomial);
                        }
                    }
                    monomials_cid.push(monomial);
                }  
                self.map_constraints_monomials.insert(c_id, monomials_cid);          
            }
        }
    }

    pub fn compute_zero_constraints(&mut self, storage: &ConstraintStorage, field: &BigInt){

        for monomial in &self.list_monomials{
            compute_zero_constraints_monomial(
                &mut self.map_constraints_monomials, 
                &mut self.map_monomials_constraints, 
                *monomial,
                storage,
                field,
            );
        }
    }


    pub fn compute_clusters_constraints(&mut self, storage: &ConstraintStorage) {

        let no_constraints = self.map_constraints_monomials.len();
        let mut arena = ClusterArena::with_capacity(no_constraints);
        let mut cluster_to_current = ClusterPath::with_capacity(no_constraints);
        let mut monomial_to_cluster = HashMap::new();
    
        for (c_id, monomials) in &self.map_constraints_monomials {
            let dest = ClusterArena::len(&arena);
            ClusterArena::push(&mut arena, Some(Cluster::new(c_id)));
            Vec::push(&mut cluster_to_current, dest);
            for monomial in monomials {
                match monomial_to_cluster.get(&monomial){
                    Some(cluster) =>{
                        let prev = cluster;
                        crate::clusters_utils::arena_merge(&mut arena, &mut cluster_to_current, *prev, dest);
                        monomial_to_cluster.insert(monomial, dest);
                    }, 
                    None => {
                        monomial_to_cluster.insert(monomial, dest);
                    },
                }
            }
        }
    
        
        self.clusters = LinkedList::new();
        for cluster in arena {
            if let Some(cluster) = cluster {
                if Cluster::size(&cluster) > 1 {
                    let mut new_storage = ConstraintStorage::new();
                    for constraint_id in cluster.constraints{
                        let constraint = storage.read_constraint(*constraint_id).unwrap();
                        let prev_constraint_id = storage.read_constraint_prev_id(*constraint_id).unwrap();
                        new_storage.add_constraint_with_prev_id(constraint, prev_constraint_id);
                    }
                    self.clusters.push_back(new_storage);
                }
            }
        } 

    }
}



fn compute_zero_constraints_monomial(
    map_constraints_monomials: &mut HashMap<ConstraintID, Vec<Monomial>>,
    map_monomials_constraints: &mut HashMap<Monomial, Vec<ConstraintID>>,
    //map_monomials_constraints: &mut HashMap<Monomial, HashSet<ConstraintID>>,
    monomial: Monomial,
    storage: &ConstraintStorage,
    field: &BigInt,
){
    match map_monomials_constraints.get(&monomial){
        Some(list_monomial) =>{
            if list_monomial.len() == 1{

                let c_id = list_monomial[0];
                let constraint = storage.read_constraint(c_id).unwrap();

                if constraint.get_value_monomial(monomial, field) != BigInt::from(0){
                    remove_zero_constraint(
                        map_constraints_monomials, 
                        map_monomials_constraints, 
                        c_id, 
                        storage, 
                        field
                    );
                }
                //let c_id = list_monomial.iter().next().unwrap();
            }
        },
        None => {}
    }
}


fn remove_zero_constraint(
    map_constraints_monomials: &mut HashMap<ConstraintID, Vec<Monomial>>,
    map_monomials_constraints: &mut HashMap<Monomial, Vec<ConstraintID>>,
    //map_monomials_constraints: &mut HashMap<Monomial, HashSet<ConstraintID>>,
    c_id: usize,
    storage: &ConstraintStorage,
    field: &BigInt,
){
    match map_constraints_monomials.get(&c_id){
        Some(list_cid) =>{

            for monomial in list_cid{
                match map_monomials_constraints.get_mut(monomial){
                    Some(list_mon) =>{
                        if let Some(pos) = list_mon.iter().position(|x| *x == c_id) {
                            list_mon.swap_remove(pos);
                        }
                        //list_mon.remove(&c_id);
                        
                    }
                    None =>{}
                }
            }
            for monomial in list_cid.clone(){
                compute_zero_constraints_monomial(
                    map_constraints_monomials,
                    map_monomials_constraints, 
                    monomial,
                    storage, 
                    field
                );
            }
            map_constraints_monomials.remove(&c_id);

        },
        None => {},
    }
}



