use circom_algebra::num_bigint::BigInt;
use circom_algebra::constraint_storage::{ ConstraintID};
use circom_algebra::simplification_utils::{Config, Simplified,  full_simplification};

use circom_algebra::algebra::{Constraint, add_linear_expression};

use std::collections::{HashSet, HashMap, LinkedList};
use super::{ConstraintStorage,  C, Monomial};
use crate::non_linear_simplification::{NonLinearConfig};

pub struct ClusterInfo{
    pub map_monomials_constraints: HashMap<Monomial, LinkedList<(ConstraintID, BigInt)>>,
    pub constraints: Vec<(C, usize)>,
}




pub fn obtain_linear_constraints(config: NonLinearConfig) -> (LinkedList<C>, LinkedList<usize>) {
    let cluster_info = compute_map_monomials(&config.storage, &config.field);
    generate_constraints(&cluster_info, &config.field)
}

pub fn compute_map_monomials(storage: &ConstraintStorage, field: &BigInt) -> ClusterInfo{

    let mut constraints = Vec::new();
    //let mut aux = Vec::new();
    let mut map_monomials_constraints: HashMap<Monomial, LinkedList<(ConstraintID, BigInt)>> = HashMap::new();
    for c_id in storage.get_ids() {
        let constraint = storage.read_constraint(c_id).unwrap();
        let prev_cid = storage.read_constraint_prev_id(c_id).unwrap();
        let monomials = constraint.take_cloned_monomials(field);
        for (monomial, coef) in monomials{
            match map_monomials_constraints.get_mut(&monomial){
                Some(list_mon) =>{
                    list_mon.push_back((c_id, coef));
                },
                None =>{
                    let mut list_mon = LinkedList::new();
                    list_mon.push_back((c_id, coef));
                    map_monomials_constraints.insert(monomial, list_mon);
                }
            }
        }
        constraints.push((constraint, prev_cid));  
        //aux.push(prev_cid);    
    }  
    //println!("Cluster con {:?}", aux);
  
    ClusterInfo{constraints, map_monomials_constraints}
}

pub fn generate_constraints(cluster_info: &ClusterInfo, field: &BigInt) 
-> (LinkedList<Constraint<usize>>, LinkedList<usize>){
    let system_constraints = generate_system_cluster(&cluster_info.map_monomials_constraints);
    // let mut j = 1;
    //     for x in system_constraints.clone(){
    //         println!("======== Equation number {:} ========",j);
    //         println!("Linear Expression A: {:?}", x.a());
    //         println!("Linear Expression B: {:?}", x.b());
    //         println!("Linear Expression C: ");
    //         for c2 in x.c().clone(){
    //             println!("     Signal: {:}",c2.0);
    //             println!("     Value : {:}",c2.1.to_string());
    //         }
    //         j = j+1;
    //     }

    let config = Config{
        field : field.clone(), 
        constraints: system_constraints, 
        forbidden: Box:: new(HashSet::new())
    };
    let simplified = full_simplification(config);
        
    get_new_constraints(&simplified, &cluster_info.constraints, field)
}





fn generate_system_cluster(
    map_monomials_constraints: &HashMap<Monomial, LinkedList<(ConstraintID, BigInt)>>
) -> LinkedList<Constraint<usize>>{
    let mut system_constraints = LinkedList::new();
    for (_, list_monomial) in map_monomials_constraints{
        let mut cons_monomial = HashMap::new();
        for (c_id, coeff) in list_monomial{
            cons_monomial.insert(c_id + 1, coeff.clone()); // SE GUARDA cid +1 PARA NO USAR EL 0
        }
        let new_constraint = Constraint::new(HashMap::new(), HashMap::new(), cons_monomial);
        system_constraints.push_back(new_constraint);
    }

    system_constraints
}

fn get_new_constraints(
    simplified: &Simplified,
    storage: &Vec<(C, usize)>,
    field: &BigInt,
)-> (LinkedList<Constraint<usize>>, LinkedList<usize>)
{
    let mut used_constraints: HashMap<ConstraintID, LinkedList<(ConstraintID, BigInt)>> = HashMap::new();
    for subs in &simplified.substitutions{
        for (c_id, coef) in subs.to(){
            if *c_id != 0{
                match used_constraints.get_mut(&(c_id-1)){
                    Some(list_cid) =>{
                        if *coef != BigInt::from(0){
                            list_cid.push_back((subs.from()-1, coef.clone()));
                        }
                    },
                    None =>{
                        let mut list_cid = LinkedList::new();
                        if *coef != BigInt::from(0){
                            list_cid.push_back((subs.from()-1, coef.clone()));

                        }
                        used_constraints.insert(c_id -1, list_cid);

                    },
                }
            }
        }
    }



    let mut new_constraints = LinkedList::new();
    let mut total_possible_eliminate = LinkedList::new();
    for (c_id, list_cid) in &used_constraints{
            let constraint = generate_new_constraint(*c_id, list_cid, storage, field);
            if !constraint.is_empty(){
                new_constraints.push_back(constraint);
                //total_possible_eliminate.push_back(storage[*c_id].1);
            }
            else{
                total_possible_eliminate.push_back(storage[*c_id].1);
            }
    }
    (new_constraints, total_possible_eliminate)
}

fn generate_new_constraint(
    c_id: ConstraintID, 
    map_cid: &LinkedList<(ConstraintID, BigInt)>,
    storage: &Vec<(C, usize)>, 
    field: &BigInt
) -> Constraint<usize>{

    let mut new_linear = storage[c_id].0.c().clone();


    let mut list =  vec!(storage[c_id].1);
    for cid in map_cid{
        list.push(storage[cid.0].1);
    }

    for (cid_aux, coef_aux) in map_cid{
        let mut c_constraint = storage[*cid_aux].0.c().clone();
        add_linear_expression(&mut new_linear, &mut c_constraint, &coef_aux, field);
    }
    let mut constraint = Constraint::new(HashMap::new(), HashMap::new(), new_linear);

    Constraint::remove_zero_value_coefficients(&mut constraint);
    constraint
}
