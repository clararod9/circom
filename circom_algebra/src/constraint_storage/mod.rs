use crate::algebra::{Constraint};
use crate::num_bigint::BigInt;
use constant_tracking::{ConstantTracker, CID};
use std::collections::{LinkedList};

mod logic;

type RawField = Vec<u8>;
type FieldTracker = ConstantTracker<RawField>;
type S = usize;
type C = Constraint<usize>;

type CompressedExpr = Vec<(CID, S)>;
type CompressedConstraint = (CompressedExpr, CompressedExpr, CompressedExpr); // A, B, C

pub type ConstraintID = usize;
pub struct ConstraintStorage {
    field_tracker: FieldTracker,
    constraints: Vec<(CompressedConstraint, usize)>,
}

impl ConstraintStorage {
    pub fn new() -> ConstraintStorage {
        ConstraintStorage { field_tracker: FieldTracker::new(), constraints: Vec::new()}
    }

    pub fn add_constraint(&mut self, constraint: C) -> ConstraintID {
        let id = self.constraints.len();
        let compressed = logic::code_constraint(constraint, &mut self.field_tracker);
        self.constraints.push((compressed, id));
        id
    }

    pub fn add_constraint_with_prev_id(&mut self, constraint: C, prev_id: usize) -> ConstraintID {
        let id = self.constraints.len();
        let compressed = logic::code_constraint(constraint, &mut self.field_tracker);
        self.constraints.push((compressed, prev_id));
        id
    }

    pub fn read_constraint(&self, id: ConstraintID) -> Option<C> {
        if id < self.constraints.len() {
            Some(logic::decode_constraint(&self.constraints[id].0, &self.field_tracker))
        } else {
            None
        }
    }

    pub fn read_constraint_prev_id(&self, id: ConstraintID) -> Option<usize> {
        if id < self.constraints.len() {
            Some(self.constraints[id].1)
        } else {
            None
        }
    }

    pub fn replace(&mut self, id: ConstraintID, new: C) {
        if id < self.constraints.len() {
            self.constraints[id].0 = logic::code_constraint(new, &mut self.field_tracker);
        }
    }



    pub fn extract_with(&mut self, filter: &dyn Fn(&C) -> bool) -> LinkedList<C> {
        let old = std::mem::take(&mut self.constraints);
        let mut removed = LinkedList::new();
        for c in old {
            let decoded = logic::decode_constraint(&c.0, &self.field_tracker);
            if filter(&decoded) {
                removed.push_back(decoded);
            } else {
                self.constraints.push(c);
            }
        }
        removed
    }

    pub fn get_ids(&self) -> Vec<ConstraintID> {
        (0..self.constraints.len()).collect()
    }

    pub fn no_constants(&self) -> CID {
        self.field_tracker.next_id()
    }

    pub fn get_no_constraints(&self) -> usize{
        self.constraints.len()
    }
}
