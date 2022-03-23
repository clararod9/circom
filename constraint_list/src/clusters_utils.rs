use std::collections::{LinkedList};


#[derive(Clone)]
pub struct Cluster<E> 
{
    pub constraints: LinkedList<E>,
}

impl <E> Default for Cluster<E> {
    fn default() -> Self { 
        Cluster{constraints: LinkedList::new()} 
    }
}

impl<E> Cluster<E>{
    pub fn new(constraint: E) -> Cluster<E> {
        let mut new = Cluster::default();
        LinkedList::push_back(&mut new.constraints, constraint);
        new
    }

    pub fn merge(mut c0: Cluster<E>, mut c1: Cluster<E>) -> Cluster<E> {
        let mut result = Cluster::default();
        LinkedList::append(&mut result.constraints, &mut c0.constraints);
        LinkedList::append(&mut result.constraints, &mut c1.constraints);
        result
    }

    pub fn size(&self) -> usize {
        LinkedList::len(&self.constraints)
    }
}

pub type ClusterArena<E> = Vec<Option<Cluster<E>>> ;
pub type ClusterPath = Vec<usize>;

pub fn shrink_jumps_and_find(c_to_c: &mut ClusterPath, org: usize) -> usize {
    let mut current = org;
    let mut jumps = Vec::new();
    while current != c_to_c[current] {
        Vec::push(&mut jumps, current);
        current = c_to_c[current];
    }
    while let Some(redirect) = Vec::pop(&mut jumps) {
        c_to_c[redirect] = current;
    }
    current
}

pub fn arena_merge<E>(arena: &mut ClusterArena<E>, c_to_c: &mut ClusterPath, src: usize, dest: usize)
{
    let current_dest = shrink_jumps_and_find(c_to_c, dest);
    let current_src = shrink_jumps_and_find(c_to_c, src);
    let c0 = std::mem::replace(&mut arena[current_dest], None).unwrap_or_default();
    let c1 = std::mem::replace(&mut arena[current_src], None).unwrap_or_default();
    let merged = Cluster::merge(c0, c1);
    arena[current_dest] = Some(merged);
    c_to_c[current_src] = current_dest;
}
