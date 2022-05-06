// Uncomment lines 163, 165, 336 and 338 to print cluster information
use super::{ConstraintStorage, EncodingIterator, SEncoded, Simplifier, A, C, S, HashConstraint};
use crate::SignalMap;
use crate::clusters_utils::{Cluster, ClusterArena, ClusterPath};

use circom_algebra::num_bigint::BigInt;
use constraint_writers::json_writer::SubstitutionJSON;
use std::collections::{HashMap, HashSet, LinkedList};
use std::sync::Arc;

const SUB_LOG: &str = "./log_substitution.json";

fn log_substitutions(substitutions: &LinkedList<S>, writer: &mut Option<SubstitutionJSON>) {
    use super::json_porting::port_substitution;
    if let Some(w) = writer {
        for s in substitutions {
            let (from, to) = port_substitution(s);
            w.write_substitution(&from, &to).unwrap();
        }
    }
}



fn build_clusters(linear: LinkedList<C>, no_vars: usize) -> Vec<Cluster<C>> {

    let no_linear = LinkedList::len(&linear);
    let mut arena = ClusterArena::with_capacity(no_linear);
    let mut cluster_to_current = ClusterPath::with_capacity(no_linear);
    let mut signal_to_cluster = vec![no_linear; no_vars];
    for constraint in linear {
        let signals = C::take_cloned_signals(&constraint);
        let dest = ClusterArena::len(&arena);
        ClusterArena::push(&mut arena, Some(Cluster::new(constraint)));
        Vec::push(&mut cluster_to_current, dest);
        for signal in signals {
            let prev = signal_to_cluster[signal];
            signal_to_cluster[signal] = dest;
            if prev < no_linear {
                crate::clusters_utils::arena_merge(&mut arena, &mut cluster_to_current, prev, dest);
            }
        }
    }
    let mut clusters = Vec::new();
    for cluster in arena {
        if let Some(cluster) = cluster {
            if Cluster::size(&cluster) != 0 {
                Vec::push(&mut clusters, cluster);
            }
        }
    }
    clusters
}

fn build_clusters_nonlinear(
    storage: &ConstraintStorage,
) -> LinkedList<ConstraintStorage> {

    let no_constraints = storage.get_no_constraints();
    let mut arena = ClusterArena::with_capacity(no_constraints);
    let mut cluster_to_current = ClusterPath::with_capacity(no_constraints);
    let mut monomial_to_cluster = HashMap::new();

    for c_id in storage.get_ids() {
        let constraint = storage.read_constraint(c_id).unwrap();
        if !constraint.is_empty(){
            let monomials = C::take_possible_cloned_monomials(&constraint);
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
    }

    let mut clusters = LinkedList::new();
    for cluster in arena {
        if let Some(cluster) = cluster {

            if cluster.size() > 1{
                let mut new_storage = ConstraintStorage::new();
    
                for constraint_id in cluster.constraints{
                    let constraint = storage.read_constraint(constraint_id).unwrap();
                    let prev_constraint_id = storage.read_constraint_prev_id(constraint_id).unwrap();
                    new_storage.add_constraint_with_prev_id(constraint, prev_constraint_id);
                }
                clusters.push_back(new_storage);
            }
        }
    }
    clusters
}

fn rebuild_witness(max_signal: usize, deleted: HashSet<usize>) -> SignalMap {
    let mut map = SignalMap::with_capacity(max_signal);
    let mut free = LinkedList::new();
    for signal in 0..max_signal {
        if deleted.contains(&signal) {
            free.push_back(signal);
        } else if let Some(new_pos) = free.pop_front() {
            map.insert(signal, new_pos);
            free.push_back(signal);
        } else {
            map.insert(signal, signal);
        }
    }
    map
}

fn eq_cluster_simplification(
    mut cluster: Cluster<C>,
    forbidden: &HashSet<usize>,
    field: &BigInt,
) -> (LinkedList<S>, LinkedList<C>) {
    if Cluster::size(&cluster) == 1 {
        let mut substitutions = LinkedList::new();
        let mut constraints = LinkedList::new();
        let constraint = LinkedList::pop_back(&mut cluster.constraints).unwrap();
        let signals: Vec<_> = C::take_cloned_signals(&constraint).iter().cloned().collect();
        let s_0 = signals[0];
        let s_1 = signals[1];
        if HashSet::contains(forbidden, &s_0) && HashSet::contains(forbidden, &s_1) {
            LinkedList::push_back(&mut constraints, constraint);
        } else if HashSet::contains(forbidden, &s_0) {
            LinkedList::push_back(
                &mut substitutions,
                S::new(s_1, A::Signal { symbol: s_0 }).unwrap(),
            );
        } else if HashSet::contains(forbidden, &s_1) {
            LinkedList::push_back(
                &mut substitutions,
                S::new(s_0, A::Signal { symbol: s_1 }).unwrap(),
            );
        } else {
            let (l, r) = if s_0 > s_1 { (s_0, s_1) } else { (s_1, s_0) };
            LinkedList::push_back(&mut substitutions, S::new(l, A::Signal { symbol: r }).unwrap());
        }
        (substitutions, constraints)
    } else {
        let mut cons = LinkedList::new();
        let mut subs = LinkedList::new();
        let (mut remains, mut min_remains) = (HashSet::new(), None);
        let (mut remove, mut min_remove) = (HashSet::new(), None);
        for c in cluster.constraints {
            for signal in C::take_cloned_signals(&c) {
                if HashSet::contains(&forbidden, &signal) {
                    HashSet::insert(&mut remains, signal);
                    min_remains = Some(min_remains.map_or(signal, |s| std::cmp::min(s, signal)));
                } else {
                    min_remove = Some(min_remove.map_or(signal, |s| std::cmp::min(s, signal)));
                    HashSet::insert(&mut remove, signal);
                }
            }
        }

        let rh_signal = if let Some(signal) = min_remains {
            HashSet::remove(&mut remains, &signal);
            signal
        } else {
            let signal = min_remove.unwrap();
            HashSet::remove(&mut remove, &signal);
            signal
        };

        for signal in remains {
            let l = A::Signal { symbol: signal };
            let r = A::Signal { symbol: rh_signal };
            let expr = A::sub(&l, &r, field);
            let c = A::transform_expression_to_constraint_form(expr, field).unwrap();
            LinkedList::push_back(&mut cons, c);
        }

        for signal in remove {
            let sub = S::new(signal, A::Signal { symbol: rh_signal }).unwrap();
            LinkedList::push_back(&mut subs, sub);
        }

        (subs, cons)
    }
}

fn eq_simplification(
    equalities: LinkedList<C>,
    forbidden: Arc<HashSet<usize>>,
    no_vars: usize,
    field: &BigInt,
    substitution_log: &mut Option<SubstitutionJSON>,
) -> (LinkedList<S>, LinkedList<C>) {
    use std::sync::mpsc;
    use threadpool::ThreadPool;

    let field = Arc::new(field.clone());
    let mut constraints = LinkedList::new();
    let mut substitutions = LinkedList::new();
    let clusters = build_clusters(equalities, no_vars);
    let (cluster_tx, simplified_rx) = mpsc::channel();
    let pool = ThreadPool::new(num_cpus::get());
    let no_clusters = Vec::len(&clusters);
    // println!("Clusters: {}", no_clusters);
    let mut single_clusters = 0;
    let mut id = 0;
    for cluster in clusters {
        if Cluster::size(&cluster) == 1 {
            let (mut subs, mut cons) = eq_cluster_simplification(cluster, &forbidden, &field);
            LinkedList::append(&mut substitutions, &mut subs);
            LinkedList::append(&mut constraints, &mut cons);
            single_clusters += 1;
        } else {
            let cluster_tx = cluster_tx.clone();
            let forbidden = Arc::clone(&forbidden);
            let field = Arc::clone(&field);
            let job = move || {
                //println!("Cluster: {}", id);
                let result = eq_cluster_simplification(cluster, &forbidden, &field);
                //println!("End of cluster: {}", id);
                cluster_tx.send(result).unwrap();
            };
            ThreadPool::execute(&pool, job);
        }
        let _ = id;
        id += 1;
    }
    // println!("{} clusters were of size 1", single_clusters);
    ThreadPool::join(&pool);
    for _ in 0..(no_clusters - single_clusters) {
        let (mut subs, mut cons) = simplified_rx.recv().unwrap();
        LinkedList::append(&mut substitutions, &mut subs);
        LinkedList::append(&mut constraints, &mut cons);
    }
    log_substitutions(&substitutions, substitution_log);
    (substitutions, constraints)
}

fn constant_eq_simplification(
    c_eq: LinkedList<C>,
    forbidden: &HashSet<usize>,
    field: &BigInt,
    substitution_log: &mut Option<SubstitutionJSON>,
) -> (LinkedList<S>, LinkedList<C>) {
    let mut cons = LinkedList::new();
    let mut subs = LinkedList::new();
    for constraint in c_eq {
        let mut signals: Vec<_> = C::take_cloned_signals(&constraint).iter().cloned().collect();
        let signal = signals.pop().unwrap();
        if HashSet::contains(&forbidden, &signal) {
            LinkedList::push_back(&mut cons, constraint);
        } else {
            let sub = C::clear_signal_from_linear(constraint, &signal, field);
            LinkedList::push_back(&mut subs, sub);
        }
    }
    log_substitutions(&subs, substitution_log);
    (subs, cons)
}

fn linear_simplification(
    log: &mut Option<SubstitutionJSON>,
    linear: LinkedList<C>,
    forbidden: Arc<HashSet<usize>>,
    no_labels: usize,
    field: &BigInt,
) -> (LinkedList<S>, LinkedList<C>) {
    use circom_algebra::simplification_utils::full_simplification;
    use circom_algebra::simplification_utils::Config;
    use std::sync::mpsc;
    use threadpool::ThreadPool;

    // println!("Cluster simplification");
    let mut cons = LinkedList::new();
    let mut substitutions = LinkedList::new();
    let clusters = build_clusters(linear, no_labels);
    let (cluster_tx, simplified_rx) = mpsc::channel();
    let pool = ThreadPool::new(num_cpus::get());
    let no_clusters = Vec::len(&clusters);
    // println!("Clusters: {}", no_clusters);
    let mut id = 0;
    for cluster in clusters {
        let cluster_tx = cluster_tx.clone();
        let config = Config {
            field: field.clone(),
            constraints: cluster.constraints,
            forbidden: Arc::clone(&forbidden),
        };
        let job = move || {
            // println!("cluster: {}", id);
            let result = full_simplification(config);
            // println!("End of cluster: {}", id);
            cluster_tx.send(result).unwrap();
        };
        ThreadPool::execute(&pool, job);
        let _ = id;
        id += 1;
    }
    ThreadPool::join(&pool);

    for _ in 0..no_clusters {
        let mut result = simplified_rx.recv().unwrap();
        log_substitutions(&result.substitutions, log);
        LinkedList::append(&mut cons, &mut result.constraints);
        LinkedList::append(&mut substitutions, &mut result.substitutions);
    }
    (substitutions, cons)
}


fn non_linear_simplification(
    log: &mut Option<SubstitutionJSON>,
    deduced_constraints_hash: &mut HashSet<HashConstraint>,
    clusters: LinkedList<ConstraintStorage>,
    forbidden: Arc<HashSet<usize>>,
    field: &BigInt,
) -> (LinkedList<S>, LinkedList<C>, LinkedList<usize>, usize) {
    use circom_algebra::simplification_utils::full_simplification;
    use circom_algebra::simplification_utils::Config;
    use std::sync::mpsc;
    use threadpool::ThreadPool;

    //println!("Cluster simplification");
    //println!("Numero total de constraints: {}", storage.get_no_constraints());
    let mut cons = LinkedList::new();
    let mut delete = LinkedList::new();
    let mut minimal_clusters = LinkedList::new();
    let (cluster_tx, simplified_rx) = mpsc::channel();
    let pool = ThreadPool::new(num_cpus::get());
    let mut no_clusters = 0;
    // println!("Clusters: {}", no_clusters);
    let mut id = 0;

    for cluster in clusters {
            no_clusters = no_clusters + 1;
            let cluster_tx = cluster_tx.clone();

            let config = crate::non_linear_simplification::NonLinearClustersConfig {
                storage: cluster,
                field: field.clone(),
            };
            let job = move || {
                let new_clusters = crate::non_linear_simplification::obtain_non_linear_clusters(config);
                cluster_tx.send(new_clusters).unwrap();
            };
            ThreadPool::execute(&pool, job);

            let _ = id;
            id += 1;
        
    }
    ThreadPool::join(&pool);
    for _ in 0..no_clusters {
        let mut new_clusters = simplified_rx.recv().unwrap();

        LinkedList::append(&mut minimal_clusters, &mut new_clusters);
    }
    //println!("Calculados clusters minimos");
    let (cluster_tx, simplified_rx) = mpsc::channel();
    let pool = ThreadPool::new(num_cpus::get());
    no_clusters = 0;
    for cluster in minimal_clusters {
        no_clusters = no_clusters + 1;
        let cluster_tx = cluster_tx.clone();

        let config = crate::non_linear_simplification::NonLinearConfig {
            field: field.clone(),
            storage: cluster,
            forbidden: Arc::clone(&forbidden),
        };

        let job = move || {
            let (new_constraints, to_delete) = crate::non_linear_simplification::deduce_linear_constraints(config);
            cluster_tx.send((new_constraints, to_delete)).unwrap();
        };
        ThreadPool::execute(&pool, job);

        let _ = id;
        id += 1;
    
    }
    ThreadPool::join(&pool);
    //println!("Calculadas nuevas lineales");
    for _ in 0..no_clusters {
        let (mut new_constraints, mut new_delete) = simplified_rx.recv().unwrap();   
        LinkedList::append(&mut cons, &mut new_constraints);
        LinkedList::append(&mut delete, &mut new_delete);
    }

    for c in &cons{
        deduced_constraints_hash.insert(C::get_hash_constraint(&c, field));
    }

    let num_new_linear = cons.len();
    let config = Config {
        field: field.clone(),
        constraints: cons,
        forbidden: Arc::clone(&forbidden),
    };


    let result = full_simplification(config);
    log_substitutions(&result.substitutions, log);
    (result.substitutions, result.constraints, delete, num_new_linear)
}

type SignalToConstraints = HashMap<usize, LinkedList<usize>>;
fn build_non_linear_signal_map(non_linear: &ConstraintStorage) -> SignalToConstraints {
    let mut map = SignalToConstraints::new();
    for c_id in non_linear.get_ids() {
        let constraint = non_linear.read_constraint(c_id).unwrap();
        for signal in C::take_cloned_signals(&constraint) {
            if let Some(list) = map.get_mut(&signal) {
                list.push_back(c_id);
            } else {
                let mut new = LinkedList::new();
                new.push_back(c_id);
                map.insert(signal, new);
            }
        }
    }

    map
}


// type SetConstraints = HashSet<(Vec<(usize, BigInt)>, Vec<(usize, BigInt)>, Vec<(usize, BigInt)>)>;

// fn build_non_linear_hashset(non_linear: &mut ConstraintStorage, field: &BigInt) -> SetConstraints {
//     let mut set = SetConstraints::new();
//     for c_id in non_linear.get_ids() {
//         let mut constraint = non_linear.read_constraint(c_id).unwrap();
//         if !C::is_empty(&constraint){
//         //     let hash = C::get_hash_constraint(&constraint, field);
//         //     if set.contains(&hash){
//         //         non_linear.replace(c_id, C::empty());
//         //     }   
//         //     else{
//                 circom_algebra::algebra::Constraint::fix_normalize_constraint(&mut constraint, field);
//                 non_linear.replace(c_id, constraint);
//         //         set.insert(hash);
//         //     }
//         }
//     }
//     set
// }


fn normalize_constraints(non_linear: &mut ConstraintStorage, field: &BigInt) {
    for c_id in non_linear.get_ids() {
        let mut constraint = non_linear.read_constraint(c_id).unwrap();
        if !C::is_empty(&constraint){

                circom_algebra::algebra::Constraint::fix_normalize_constraint(&mut constraint, field);
                non_linear.replace(c_id, constraint);
        }
    }
}


fn apply_substitution_to_map(
    storage: &mut ConstraintStorage,
    map: &mut SignalToConstraints,
    substitutions: &LinkedList<S>,
    field: &BigInt,
) -> LinkedList<C> {
    fn constraint_processing(
        storage: &mut ConstraintStorage,
        map: &mut SignalToConstraints,
        c_ids: &LinkedList<usize>,
        substitution: &S,
        field: &BigInt,
    ) -> LinkedList<usize> {
        let mut linear = LinkedList::new();
        let signals: LinkedList<_> = substitution.to().keys().cloned().collect();
        for c_id in c_ids {
            let c_id = *c_id;
            let mut constraint = storage.read_constraint(c_id).unwrap();
            C::apply_substitution(&mut constraint, substitution, field);
            if C::is_linear(&constraint) {
                linear.push_back(c_id);
            }
            storage.replace(c_id, constraint);
            for signal in &signals {
                if let Some(list) = map.get_mut(&signal) {
                    list.push_back(c_id);
                } else {
                    let mut new = LinkedList::new();
                    new.push_back(c_id);
                    map.insert(*signal, new);
                }
            }
        }
        linear
    }

    let mut linear_id = LinkedList::new();
    for substitution in substitutions {
        if let Some(c_ids) = map.get(substitution.from()).cloned() {
            let mut new_linear = constraint_processing(storage, map, &c_ids, substitution, field);
            linear_id.append(&mut new_linear);
        }
    }
    let mut linear = LinkedList::new();
    for c_id in linear_id {
        let constraint = storage.read_constraint(c_id).unwrap();
        if !C::is_empty(&constraint){
            linear.push_back(constraint);
            storage.replace(c_id, C::empty());
        }
    }
    linear
}


fn apply_substitution_to_map_non_linear(
    storage: &mut ConstraintStorage,
    map: &mut SignalToConstraints,
    substitutions: &LinkedList<S>,
    field: &BigInt,
) -> LinkedList<C> {
    fn constraint_processing(
        storage: &mut ConstraintStorage,
        map: &mut SignalToConstraints,
        c_ids: &LinkedList<usize>,
        substitution: &S,
        field: &BigInt,
    ) -> LinkedList<usize> {
        let mut linear = LinkedList::new();
        let signals: LinkedList<_> = substitution.to().keys().cloned().collect();
        for c_id in c_ids {
            let c_id = *c_id;
            let mut constraint = storage.read_constraint(c_id).unwrap();
            C::apply_substitution_normalize(&mut constraint, substitution, field);
            if C::is_linear(&constraint) {
                linear.push_back(c_id);
            }
            storage.replace(c_id, constraint);
            for signal in &signals {
                if let Some(list) = map.get_mut(&signal) {
                    list.push_back(c_id);
                } else {
                    let mut new = LinkedList::new();
                    new.push_back(c_id);
                    map.insert(*signal, new);
                }
            }
        }
        linear
    }

    let mut linear_id = LinkedList::new();
    for substitution in substitutions {
        if let Some(c_ids) = map.get(substitution.from()).cloned() {
            let mut new_linear = constraint_processing(storage, map, &c_ids, substitution, field);
            linear_id.append(&mut new_linear);
        }
    }
    let mut linear = LinkedList::new();
    for c_id in linear_id {
        let constraint = storage.read_constraint(c_id).unwrap();
        if !C::is_empty(&constraint){
            linear.push_back(constraint);
            storage.replace(c_id, C::empty());
        }
    }
    linear
}

pub fn _get_affected_constraints(
    storage: &ConstraintStorage,
    map: &SignalToConstraints,
    substitutions: &LinkedList<S>
)-> LinkedList<ConstraintStorage>{
    
    let mut affected = LinkedList::new();
    for subs in substitutions{
        let mut set_new = HashSet::new();
        let mut new = ConstraintStorage::new();
        for (signal, _coef) in subs.to(){
            if *signal != 0{
                for cid in map.get(signal).unwrap(){
                    set_new.insert(*cid);
                }
            }           
        }

        for cid in set_new{
            let constraint = storage.read_constraint(cid).unwrap();
            if !constraint.is_empty(){
                new.add_constraint_with_prev_id(constraint, cid);
            }
        }
        affected.push_back(new);
    }
    affected
}

// struct ResultSubstitution {
//     linear: LinkedList<C>,
//     eliminated: usize,
// }

// fn apply_substitution_to_map_non_linear1(
//     storage: &mut ConstraintStorage,
//     map: &mut SignalToConstraints,
//     set: &mut SetConstraints,
//     substitutions: &LinkedList<S>,
//     field: &BigInt,
// ) -> ResultSubstitution {
//     fn constraint_processing(
//         storage: &mut ConstraintStorage,
//         map: &mut SignalToConstraints,
//         set: &mut SetConstraints,
//         c_ids: &LinkedList<usize>,
//         substitution: &S,
//         field: &BigInt,
//     ) -> (LinkedList<usize>, usize) {
//         let mut linear = LinkedList::new();
//         let mut eliminated = 0;
//         let signals: LinkedList<_> = substitution.to().keys().cloned().collect();
//         for c_id in c_ids {
//             let c_id = *c_id;
//             let mut constraint = storage.read_constraint(c_id).unwrap();
//             let prev_hash = C::get_hash_constraint(&constraint, &field);
//             set.remove(&prev_hash);
//             C::apply_substitution_normalize(&mut constraint, substitution, field);
//             if C::is_linear(&constraint) {
//                 linear.push_back(c_id);
//             }
//             let hash = C::get_hash_constraint(&constraint, &field);
//             if !set.contains(&hash){
//                 set.insert(hash);
//                 storage.replace(c_id, constraint);
//                 for signal in &signals {
//                     if let Some(list) = map.get_mut(&signal) {
//                         list.push_back(c_id);
//                     } else {
//                         let mut new = LinkedList::new();
//                         new.push_back(c_id);
//                         map.insert(*signal, new);
//                     }
//                 }
//             }
//             else{
//                 storage.replace(c_id, C::empty());
//                 eliminated = eliminated + 1;
//             }
//         }
//         (linear, eliminated)
//     }

//     let mut linear_id = LinkedList::new();
//     let mut total_eliminated = 0;
//     for substitution in substitutions {
//         if let Some(c_ids) = map.get(substitution.from()).cloned() {
//             let (mut new_linear, eliminated) = constraint_processing(storage, map, set, &c_ids, substitution, field);
//             total_eliminated = total_eliminated + eliminated;
//             linear_id.append(&mut new_linear);
//         }
//     }
//     let mut linear = LinkedList::new();
//     for c_id in linear_id {
//         let constraint = storage.read_constraint(c_id).unwrap();
//         if !C::is_empty(&constraint){
//             linear.push_back(constraint);
//             storage.replace(c_id, C::empty());
//             total_eliminated = total_eliminated + 1;
//         }
//     }
    
//     ResultSubstitution{ linear: linear, eliminated: total_eliminated}
// }





fn build_relevant_set(
    mut iter: EncodingIterator,
    relevant: &mut HashSet<usize>,
    renames: &SEncoded,
    deletes: &SEncoded,
) {
    fn unwrapped_signal(map: &SEncoded, signal: usize) -> Option<usize> {
        let f = |e: &A| {
            if let A::Signal { symbol } = e {
                Some(*symbol)
            } else {
                None
            }
        };
        SEncoded::get(map, &signal).map_or(None, f)
    }

    let (_, non_linear) = EncodingIterator::take(&mut iter);
    for c in non_linear {
        for signal in C::take_cloned_signals(&c) {
            let signal = unwrapped_signal(renames, signal).unwrap_or(signal);
            if !SEncoded::contains_key(deletes, &signal) {
                HashSet::insert(relevant, signal);
            }
        }
    }

    for edge in EncodingIterator::edges(&iter) {
        let next = EncodingIterator::next(&iter, edge);
        build_relevant_set(next, relevant, renames, deletes)
    }
}

fn remove_not_relevant(substitutions: &mut SEncoded, relevant: &HashSet<usize>) {
    let signals: Vec<_> = substitutions.keys().cloned().collect();
    for signal in signals {
        if !HashSet::contains(&relevant, &signal) {
            SEncoded::remove(substitutions, &signal);
        }
    }
}

// fn remove_redundant_constraints(constraint_storage: &mut ConstraintStorage, field: &BigInt){
//     let mut set_constraints = HashSet::new();
//     for cid in constraint_storage.get_ids(){
//         let constraint = constraint_storage.read_constraint(cid).unwrap();
//         let hash_constraint = C::get_hash_constraint(&constraint, field);
//         if set_constraints.contains(&hash_constraint){
//             constraint_storage.replace(cid, C::empty());
//         }
//         else{
//             set_constraints.insert(hash_constraint);
//         }
//     }
// }

pub fn simplification(smp: &mut Simplifier) -> (ConstraintStorage, SignalMap) {
    use super::non_linear_utils::obtain_and_simplify_non_linear;
    use circom_algebra::simplification_utils::build_encoded_fast_substitutions;
    use circom_algebra::simplification_utils::fast_encoded_constraint_substitution;
    use std::time::SystemTime;

    let mut substitution_log =
        if smp.port_substitution { Some(SubstitutionJSON::new(SUB_LOG).unwrap()) } else { None };
    let apply_linear = !smp.flag_s;
    let apply_non_linear = true;
    let field = smp.field.clone();
    let forbidden = Arc::new(std::mem::replace(&mut smp.forbidden, HashSet::with_capacity(0)));
    let no_labels = Simplifier::no_labels(smp);
    let equalities = std::mem::replace(&mut smp.equalities, LinkedList::new());
    let max_signal = smp.max_signal;
    let mut cons_equalities = std::mem::replace(&mut smp.cons_equalities, LinkedList::new());
    let mut linear = std::mem::replace(&mut smp.linear, LinkedList::new());
    let mut deleted = HashSet::new();
    let mut lconst = LinkedList::new();
    let mut no_rounds = smp.no_rounds;

    let relevant_signals = {
        // println!("Creating first relevant set");
        let now = SystemTime::now();
        let mut relevant = HashSet::new();
        let iter = EncodingIterator::new(&smp.dag_encoding);
        let s_sub = HashMap::with_capacity(0);
        let c_sub = HashMap::with_capacity(0);
        build_relevant_set(iter, &mut relevant, &s_sub, &c_sub);
        let _dur = now.elapsed().unwrap().as_millis();
        // println!("First relevant set created: {} ms", dur);
        relevant
    };

    let single_substitutions = {
        // println!("Start of single assignment simplification");
        let now = SystemTime::now();
        let (subs, mut cons) = eq_simplification(
            equalities,
            Arc::clone(&forbidden),
            no_labels,
            &field,
            &mut substitution_log,
        );

        LinkedList::append(&mut lconst, &mut cons);
        let mut substitutions = build_encoded_fast_substitutions(subs);
        for constraint in &mut linear {
            fast_encoded_constraint_substitution(constraint, &substitutions, &field);
        }
        for constraint in &mut cons_equalities {
            fast_encoded_constraint_substitution(constraint, &substitutions, &field);
        }
        for signal in substitutions.keys().cloned() {
            deleted.insert(signal);
        }
        remove_not_relevant(&mut substitutions, &relevant_signals);
        let _dur = now.elapsed().unwrap().as_millis();
        // println!("End of single assignment simplification: {} ms", dur);
        substitutions
    };

    let cons_substitutions = {
        // println!("Start of constant assignment simplification");
        let now = SystemTime::now();
        let (subs, mut cons) =
            constant_eq_simplification(cons_equalities, &forbidden, &field, &mut substitution_log);
        LinkedList::append(&mut lconst, &mut cons);
        let substitutions = build_encoded_fast_substitutions(subs);
        for constraint in &mut linear {
            fast_encoded_constraint_substitution(constraint, &substitutions, &field);
        }
        for signal in substitutions.keys().cloned() {
            deleted.insert(signal);
        }
        let _dur = now.elapsed().unwrap().as_millis();
        // println!("End of constant assignment simplification: {} ms", dur);
        substitutions
    };

    let relevant_signals = {
        // println!("Start building relevant");
        let now = SystemTime::now();
        let mut relevant = HashSet::new();
        let iter = EncodingIterator::new(&smp.dag_encoding);
        build_relevant_set(iter, &mut relevant, &single_substitutions, &cons_substitutions);
        let _dur = now.elapsed().unwrap().as_millis();
        // println!("Relevant built: {} ms", dur);
        relevant
    };

    let linear_substitutions = if apply_linear {
        let now = SystemTime::now();
        let (subs, mut cons) = linear_simplification(
            &mut substitution_log,
            linear,
            Arc::clone(&forbidden),
            no_labels,
            &field,
        );
        // println!("Building substitution map");
        let now0 = SystemTime::now();
        let mut only_relevant = LinkedList::new();
        for substitution in subs {
            deleted.insert(*substitution.from());
            if relevant_signals.contains(substitution.from()) {
                only_relevant.push_back(substitution);
            }
        }
        let substitutions = build_encoded_fast_substitutions(only_relevant);
        let _dur0 = now0.elapsed().unwrap().as_millis();
        // println!("End of substitution map: {} ms", dur0);
        let _dur = now.elapsed().unwrap().as_millis();
        // println!("End of cluster simplification: {} ms", dur);
        LinkedList::append(&mut lconst, &mut cons);
        for constraint in &mut lconst {
            fast_encoded_constraint_substitution(constraint, &substitutions, &field);
        }
        substitutions
    } else {
        LinkedList::append(&mut lconst, &mut linear);
        HashMap::with_capacity(0)
    };

    let (with_linear, mut constraint_storage) = {
        // println!("Building constraint storage");
        let now = SystemTime::now();
        let mut frames = LinkedList::new();
        LinkedList::push_back(&mut frames, single_substitutions);
        LinkedList::push_back(&mut frames, cons_substitutions);
        LinkedList::push_back(&mut frames, linear_substitutions);
        let iter = EncodingIterator::new(&smp.dag_encoding);
        let mut storage = ConstraintStorage::new();
        let with_linear = obtain_and_simplify_non_linear(iter, &mut storage, &frames, &field);
        crate::state_utils::empty_encoding_constraints(&mut smp.dag_encoding);
        let _dur = now.elapsed().unwrap().as_millis();
        // println!("Storages built in {} ms", dur);
        no_rounds -= 1;
        (with_linear, storage)
    };

    let mut round_id = 0;
    let _ = round_id;
    let mut linear = with_linear;
    let mut apply_round = apply_linear && no_rounds > 0 && !linear.is_empty();
    let mut non_linear_map = if apply_round  || apply_non_linear{
        // println!("Building non-linear map");
        let now = SystemTime::now();
        let non_linear_map = build_non_linear_signal_map(&constraint_storage);
        let _dur = now.elapsed().unwrap().as_millis();
        // println!("Non-linear was built in {} ms", dur);
        non_linear_map
    } else {
        SignalToConstraints::with_capacity(0)
    };
    while apply_round {
        let now = SystemTime::now();
        // println!("Number of linear constraints: {}", linear.len());
        let (substitutions, mut constants) = linear_simplification(
            &mut substitution_log,
            linear,
            Arc::clone(&forbidden),
            no_labels,
            &field,
        );

        for sub in &substitutions {
            deleted.insert(*sub.from());
        }
        lconst.append(&mut constants);
        for constraint in &mut lconst {
            for substitution in &substitutions {
                C::apply_substitution(constraint, substitution, &field);
            }
        }
        linear = apply_substitution_to_map(
            &mut constraint_storage,
            &mut non_linear_map,
            &substitutions,
            &field,
        );
        round_id += 1;
        no_rounds -= 1;
        apply_round = !linear.is_empty() && no_rounds > 0;
        let _dur = now.elapsed().unwrap().as_millis();
        // println!("Iteration no {} took {} ms", round_id, dur);
    }

    for constraint in linear {
        constraint_storage.add_constraint(constraint);
    }
    for constraint in lconst {
        constraint_storage.add_constraint(constraint);
    }


    let mut apply_round_non_linear = true;
    let mut total_eliminated = 0;
    let mut linear_extracted_non_linear = 0;
    let mut linear_obtained_after_simplification = 0;
    let mut iterations_non_linear = 0;
    let mut iterations_linear = 0;
    let mut deduced_constraints = HashSet::new();


    //let mut non_linear_set = build_non_linear_hashset(&mut constraint_storage, &field);
    normalize_constraints(&mut constraint_storage, &field);


    let mut new_clusters  = build_clusters_nonlinear(&constraint_storage);
    let now = SystemTime::now();

    while apply_round_non_linear{
        //println!("Numero de clusters {}", new_clusters.len());
        let (substitutions, _, to_delete, num_new_linear) = non_linear_simplification(
            &mut substitution_log,
            &mut deduced_constraints,
            new_clusters,
            Arc::clone(&forbidden),
            &field,
        );

        linear_extracted_non_linear = linear_extracted_non_linear + num_new_linear;

        //println!("Calculadas substituciones");
        for sub in &substitutions {
            deleted.insert(*sub.from());
        }
        

        let mut linear = apply_substitution_to_map_non_linear(
            &mut constraint_storage,
            &mut non_linear_map,
            //&mut non_linear_set,
            &substitutions,
            &field,
        );

        //let mut affected_constraints = get_affected_constraints(&constraint_storage, &non_linear_map, &substitutions);

        // println!("------------Eliminacion no lineal---------------");
        // println!("Numero de nuevas lineales: {}", linear.len());
        // println!("Numero de señales eliminadas: {}", substitutions.len());

        let mut apply_round_linear = !linear.is_empty();
        apply_round_non_linear = substitutions.len() > 0|| !to_delete.is_empty();
        if substitutions.len() > 0 {
            iterations_non_linear = iterations_non_linear + 1;
        }

        while apply_round_linear {
            linear_obtained_after_simplification = linear_obtained_after_simplification + linear.len();

            let now = SystemTime::now();
            // println!("Number of linear constraints: {}", linear.len());
            let (substitutions, _) = linear_simplification(
                &mut substitution_log,
                linear,
                Arc::clone(&forbidden),
                no_labels,
                &field,
            );
    
            for sub in &substitutions {
                deleted.insert(*sub.from());
            }

            linear = apply_substitution_to_map_non_linear(
                &mut constraint_storage,
               &mut non_linear_map,
               //&mut non_linear_set,
               &substitutions,
               &field,
           );

            //affected_constraints.append(&mut get_affected_constraints(&constraint_storage, &non_linear_map, &substitutions));

            total_eliminated = total_eliminated + substitutions.len();

            // println!("------------Eliminacion lineal---------------");
            // println!("Numero de eliminadas: {}", substitutions.len());
            // println!("Numero de nuevas lineales: {}", linear.len());

            apply_round_linear = !linear.is_empty();
            let _dur = now.elapsed().unwrap().as_millis();

            if substitutions.len() > 0 {
                iterations_linear = iterations_linear + 1;
            }
            // println!("Iteration no {} took {} ms", round_id, dur);
        }
        for constraint in linear {
            constraint_storage.add_constraint(constraint);
        }

        //println!("Posibles eliminaciones {:?}", to_delete.len());
        for possible_delete in to_delete{
            
            if !constraint_storage.read_constraint(possible_delete).unwrap().is_empty() {
                total_eliminated = total_eliminated + 1;
                constraint_storage.replace(possible_delete, C::empty());
            }
        }

        new_clusters = build_clusters_nonlinear(&constraint_storage);


    }


    //}
    

    println!("--------------COMPLETED SIMPLIFICATION----------------");    
    println!("Number of eliminated constraints: {}", total_eliminated);
    println!("Number of lineal constraints deduced from non-linear constraints: {}", linear_extracted_non_linear);
    //println!("Number of different lineal constraints deduced from non-linear constraints: {}", deduced_constraints.len());
    println!("Number of lineal constraints obtained via simplifications: {}", linear_obtained_after_simplification);
    println!("Number of iterations: {}", iterations_non_linear);
    let dur = now.elapsed().unwrap().as_millis();
    println!("TIME: {} ms", dur);
    println!("-----------------------------------------------------"); 

    //remove_redundant_constraints(&mut constraint_storage, &field);

    // //let clusters = get_clusters_quadratic_equalities(&constraint_storage, no_labels);
    // let (clusters_definitions, signal_to_clusters) = get_clusters_definitions(&constraint_storage, no_labels);

    // let (once_shared, possible_combinations) = generate_possible_combinations_clusters(&signal_to_clusters);

    // println!("Numero de clusters: {}", clusters_definitions.len());
    // for cluster in &clusters_definitions{
    //     println!("Numero de constraints en el cluster: {}", cluster.constraints.len());
    // }

    // println!("Numero de coinciden 1: {}", once_shared.len());
    // for combination in once_shared{
    //     println!("Combinacion: {:?}", combination);
    //     println!("Mostrando tamaño del primer cluster {:?}", clusters_definitions[combination.0].constraints.len());
    //     println!("Mostrando tamaño del segundo cluster {:?}", clusters_definitions[combination.1].constraints.len());
    // }

    // println!("Numero de combinaciones: {}", possible_combinations.len());
    // for combination in possible_combinations{
    //     println!("Combinacion: {:?}", combination);
    // }

    let _trash = constraint_storage.extract_with(&|c| C::is_empty(c));

    println!("Number of constraints after simplification: {}", constraint_storage.get_no_constraints());

    let signal_map = {
        // println!("Rebuild witness");
        let now = SystemTime::now();
        let signal_map = rebuild_witness(max_signal, deleted);
        let _dur = now.elapsed().unwrap().as_millis();
        // println!("End of rebuild witness: {} ms", dur);
        signal_map
    };


    if let Some(w) = substitution_log {
        w.end().unwrap();
    }
    // println!("NO CONSTANTS: {}", constraint_storage.no_constants());
    (constraint_storage, signal_map)
}
