use super::modular_arithmetic;
pub use super::modular_arithmetic::ArithmeticError;
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};
use std::collections::{HashMap, HashSet, LinkedList};
use std::fmt::{Display, Formatter};
use std::hash::Hash;

pub enum ArithmeticExpression<C>
where
    C: Hash + Eq,
{
    Number {
        value: BigInt,
    },
    Signal {
        symbol: C,
    },
    Linear {
        // Represents the expression: c1*s1 + .. + cn*sn + C
        // where c1..cn are integers modulo a prime and
        // s1..sn are signals. C is a constant value
        coefficients: HashMap<C, BigInt>,
    },
    Quadratic {
        // Is a quadratic expression of the form:
        //              a*b + c
        // Where a,b and c are linear expression
        a: HashMap<C, BigInt>,
        b: HashMap<C, BigInt>,
        c: HashMap<C, BigInt>,
    },
    NonQuadratic,
}
impl<C: Default + Clone + Display + Hash + Eq> Display for ArithmeticExpression<C> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use ArithmeticExpression::*;
        let msg = match self {
            Number { value } => value.to_str_radix(10),
            Signal { symbol } => format!("{}", symbol),
            NonQuadratic => "Non quadratic".to_string(),
            Linear { coefficients } => ArithmeticExpression::string_from_coefficients(coefficients),
            Quadratic { a, b, c } => {
                let a_string = ArithmeticExpression::string_from_coefficients(a);
                let b_string = ArithmeticExpression::string_from_coefficients(b);
                let c_string = ArithmeticExpression::string_from_coefficients(c);
                format!("({})*({}) + ({})", a_string, b_string, c_string)
            }
        };
        f.write_str(msg.as_str())
    }
}

impl<C: Default + Clone + Display + Hash + Eq> Clone for ArithmeticExpression<C> {
    fn clone(&self) -> Self {
        use ArithmeticExpression::*;
        match self {
            Number { value } => Number { value: value.clone() },
            Signal { symbol } => Signal { symbol: symbol.clone() },
            Linear { coefficients } => Linear { coefficients: coefficients.clone() },
            Quadratic { a, b, c } => Quadratic { a: a.clone(), b: b.clone(), c: c.clone() },
            NonQuadratic => NonQuadratic,
        }
    }
}

impl<C: Default + Clone + Display + Hash + Eq> Eq for ArithmeticExpression<C> {}
impl<C: Default + Clone + Display + Hash + Eq> PartialEq for ArithmeticExpression<C> {
    fn eq(&self, other: &Self) -> bool {
        use ArithmeticExpression::*;
        match (self, other) {
            (Number { value: v_0 }, Number { value: v_1 }) => *v_0 == *v_1,
            (Signal { symbol: s_0 }, Signal { symbol: s_1 }) => *s_0 == *s_1,
            (Linear { coefficients: c_0 }, Linear { coefficients: c_1 }) => *c_0 == *c_1,
            (Quadratic { a: a_0, b: b_0, c: c_0 }, Quadratic { a: a_1, b: b_1, c: c_1 }) => {
                *a_0 == *a_1 && *b_0 == *b_1 && *c_0 == *c_1
            }
            _ => false,
        }
    }
}

impl<C: Default + Clone + Display + Hash + Eq> Default for ArithmeticExpression<C> {
    fn default() -> Self {
        ArithmeticExpression::NonQuadratic
    }
}

impl<C: Default + Clone + Display + Hash + Eq> ArithmeticExpression<C> {
    pub fn new() -> ArithmeticExpression<C> {
        ArithmeticExpression::default()
    }

    // printing utils
    fn string_from_coefficients(coefficients: &HashMap<C, BigInt>) -> String {
        let mut string_coefficients = "".to_string();
        for (signal, value) in coefficients {
            let component_string = if value.is_zero() {
                "".to_string()
            } else if signal.eq(&ArithmeticExpression::constant_coefficient()) {
                format!("{}+", value.to_str_radix(10))
            } else {
                format!("{}*{}+", signal, value.to_str_radix(10))
            };
            string_coefficients.push_str(component_string.as_str());
        }
        string_coefficients.pop();
        string_coefficients
    }

    // constraint generation utils
    // transforms constraints into a constraint, None if the expression was non-quadratic
    pub fn transform_expression_to_constraint_form(
        arithmetic_expression: ArithmeticExpression<C>,
        field: &BigInt,
    ) -> Option<Constraint<C>> {
        use ArithmeticExpression::*;
        let mut a = HashMap::new();
        let mut b = HashMap::new();
        let mut c = HashMap::new();
        ArithmeticExpression::initialize_hashmap_for_expression(&mut a);
        ArithmeticExpression::initialize_hashmap_for_expression(&mut b);
        ArithmeticExpression::initialize_hashmap_for_expression(&mut c);
        match arithmetic_expression {
            NonQuadratic => {
                return Option::None;
            }
            Quadratic { a: old_a, b: old_b, c: old_c } => {
                a = old_a;
                b = old_b;
                c = old_c;
            }
            Number { value } => {
                c.insert(ArithmeticExpression::constant_coefficient(), value);
            }
            Signal { symbol } => {
                c.insert(symbol, BigInt::from(1));
            }
            Linear { coefficients } => {
                c = coefficients;
            }
        }
        ArithmeticExpression::multiply_coefficients_by_constant(&BigInt::from(-1), &mut c, field);
        Option::Some(Constraint::new(a, b, c))
    }

    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // All the operations must ensure that the Hashmaps used
    // to construct Expressions contain the empty string
    // as key.
    // Therefore the function 'initialize_hashmap_for_expression'
    // is meant to be call each time a hashmap is going to be
    // part of a Expression
    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    fn constant_coefficient() -> C {
        C::default()
    }
    fn initialize_hashmap_for_expression(initial: &mut HashMap<C, BigInt>) {
        initial
            .entry(ArithmeticExpression::constant_coefficient())
            .or_insert_with(|| BigInt::from(0));
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(initial));
    }
    fn valid_hashmap_for_expression(h: &HashMap<C, BigInt>) -> bool {
        let cc = ArithmeticExpression::constant_coefficient();
        h.contains_key(&cc)
    }
    fn initialize_symbol_in_coefficients(symbol: &C, coefficients: &mut HashMap<C, BigInt>) {
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients));
        if !coefficients.contains_key(symbol) {
            coefficients.insert(symbol.clone(), BigInt::from(0));
        }
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients));
    }
    fn add_constant_to_coefficients(
        value: &BigInt,
        coefficients: &mut HashMap<C, BigInt>,
        field: &BigInt,
    ) {
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients));
        let cc: C = ArithmeticExpression::constant_coefficient();
        coefficients.insert(
            cc.clone(),
            modular_arithmetic::add(coefficients.get(&cc).unwrap(), value, field),
        );
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients));
    }
    fn add_symbol_to_coefficients(
        symbol: &C,
        coefficient: &BigInt,
        coefficients: &mut HashMap<C, BigInt>,
        field: &BigInt,
    ) {
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients));
        ArithmeticExpression::initialize_symbol_in_coefficients(symbol, coefficients);
        coefficients.insert(
            symbol.clone(),
            modular_arithmetic::add(coefficients.get(symbol).unwrap(), coefficient, field),
        );
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients));
    }
    fn add_coefficients_to_coefficients(
        coefficients_0: &HashMap<C, BigInt>,
        coefficients_1: &mut HashMap<C, BigInt>,
        field: &BigInt,
    ) {
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients_0));
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients_1));
        for (symbol, coefficient) in coefficients_0 {
            ArithmeticExpression::add_symbol_to_coefficients(
                symbol,
                coefficient,
                coefficients_1,
                field,
            );
        }
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients_0));
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients_1));
    }
    fn multiply_coefficients_by_constant(
        constant: &BigInt,
        coefficients: &mut HashMap<C, BigInt>,
        field: &BigInt,
    ) {
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients));
        for value in coefficients.values_mut() {
            *value = modular_arithmetic::mul(value, constant, field);
        }
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients));
    }
    fn divide_coefficients_by_constant(
        constant: &BigInt,
        coefficients: &mut HashMap<C, BigInt>,
        field: &BigInt,
    ) -> Result<(), ArithmeticError> {
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients));
        for value in coefficients.values_mut() {
            *value = modular_arithmetic::div(value, constant, field)?;
        }
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients));
        Result::Ok(())
    }
    fn idivide_coefficients_by_constant(
        constant: &BigInt,
        coefficients: &mut HashMap<C, BigInt>,
        field: &BigInt,
    ) -> Result<(), ArithmeticError> {
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients));
        for value in coefficients.values_mut() {
            *value = modular_arithmetic::idiv(value, constant, field)?;
        }
        debug_assert!(ArithmeticExpression::valid_hashmap_for_expression(coefficients));
        Result::Ok(())
    }

    pub fn add(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        match (left, right) {
            (NonQuadratic, _) | (_, NonQuadratic) | (Quadratic { .. }, Quadratic { .. }) => {
                NonQuadratic
            }
            (Number { value: v_0 }, Number { value: v_1 }) => {
                Number { value: modular_arithmetic::add(v_0, v_1, field) }
            }
            (Number { value }, Signal { symbol }) | (Signal { symbol }, Number { value }) => {
                let mut coefficients = HashMap::new();
                ArithmeticExpression::initialize_hashmap_for_expression(&mut coefficients);
                ArithmeticExpression::add_constant_to_coefficients(value, &mut coefficients, field);
                ArithmeticExpression::add_symbol_to_coefficients(
                    symbol,
                    &BigInt::from(1),
                    &mut coefficients,
                    field,
                );
                Linear { coefficients }
            }
            (Number { value }, Linear { coefficients })
            | (Linear { coefficients }, Number { value }) => {
                let mut n_coefficients = coefficients.clone();
                ArithmeticExpression::add_constant_to_coefficients(
                    value,
                    &mut n_coefficients,
                    field,
                );
                Linear { coefficients: n_coefficients }
            }
            (Number { value }, Quadratic { a, b, c })
            | (Quadratic { a, b, c }, Number { value }) => {
                let mut n_c = c.clone();
                ArithmeticExpression::add_constant_to_coefficients(value, &mut n_c, field);
                Quadratic { a: a.clone(), b: b.clone(), c: n_c }
            }
            (Signal { symbol: symbol_0 }, Signal { symbol: symbol_1 }) => {
                let mut coefficients = HashMap::new();
                ArithmeticExpression::initialize_hashmap_for_expression(&mut coefficients);
                ArithmeticExpression::add_symbol_to_coefficients(
                    symbol_0,
                    &BigInt::from(1),
                    &mut coefficients,
                    field,
                );
                ArithmeticExpression::add_symbol_to_coefficients(
                    symbol_1,
                    &BigInt::from(1),
                    &mut coefficients,
                    field,
                );
                Linear { coefficients }
            }
            (Signal { symbol }, Linear { coefficients })
            | (Linear { coefficients }, Signal { symbol }) => {
                let mut n_coefficients = coefficients.clone();
                ArithmeticExpression::add_symbol_to_coefficients(
                    symbol,
                    &BigInt::from(1),
                    &mut n_coefficients,
                    field,
                );
                Linear { coefficients: n_coefficients }
            }
            (Signal { symbol }, Quadratic { a, b, c })
            | (Quadratic { a, b, c }, Signal { symbol }) => {
                let mut coefficients = c.clone();
                ArithmeticExpression::add_symbol_to_coefficients(
                    symbol,
                    &BigInt::from(1),
                    &mut coefficients,
                    field,
                );
                Quadratic { a: a.clone(), b: b.clone(), c: coefficients }
            }
            (Linear { coefficients: coefficients_0 }, Linear { coefficients: coefficients_1 }) => {
                let mut n_coefficients = coefficients_1.clone();
                ArithmeticExpression::add_coefficients_to_coefficients(
                    coefficients_0,
                    &mut n_coefficients,
                    field,
                );
                Linear { coefficients: n_coefficients }
            }
            (Linear { coefficients }, Quadratic { a, b, c })
            | (Quadratic { a, b, c }, Linear { coefficients }) => {
                let mut coefficients_1 = c.clone();
                ArithmeticExpression::add_coefficients_to_coefficients(
                    coefficients,
                    &mut coefficients_1,
                    field,
                );
                Quadratic { a: a.clone(), b: b.clone(), c: coefficients_1 }
            }
        }
    }

    pub fn mul(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        match (left, right) {
            (NonQuadratic, _)
            | (_, NonQuadratic)
            | (Quadratic { .. }, Quadratic { .. })
            | (Quadratic { .. }, Linear { .. })
            | (Linear { .. }, Quadratic { .. })
            | (Quadratic { .. }, Signal { .. })
            | (Signal { .. }, Quadratic { .. }) => NonQuadratic,
            (Number { value: value_0 }, Number { value: value_1 }) => {
                Number { value: modular_arithmetic::mul(value_0, value_1, field) }
            }
            (Number { value }, Signal { symbol }) | (Signal { symbol }, Number { value }) => {
                let mut coefficients = HashMap::new();
                ArithmeticExpression::initialize_hashmap_for_expression(&mut coefficients);
                ArithmeticExpression::add_symbol_to_coefficients(
                    symbol,
                    value,
                    &mut coefficients,
                    field,
                );
                Linear { coefficients }
            }
            (Number { value }, Linear { coefficients })
            | (Linear { coefficients }, Number { value }) => {
                let mut n_coefficients = coefficients.clone();
                ArithmeticExpression::multiply_coefficients_by_constant(
                    value,
                    &mut n_coefficients,
                    field,
                );
                Linear { coefficients: n_coefficients }
            }
            (Number { value }, Quadratic { a, b, c })
            | (Quadratic { a, b, c }, Number { value }) => {
                let mut n_a = a.clone();
                let n_b = b.clone();
                let mut n_c = c.clone();
                ArithmeticExpression::multiply_coefficients_by_constant(value, &mut n_a, field);
                ArithmeticExpression::multiply_coefficients_by_constant(value, &mut n_c, field);
                Quadratic { a: n_a, b: n_b, c: n_c }
            }
            (Signal { symbol: symbol_0 }, Signal { symbol: symbol_1 }) => {
                let mut a = HashMap::new();
                let mut b = HashMap::new();
                let mut c = HashMap::new();
                ArithmeticExpression::initialize_hashmap_for_expression(&mut a);
                ArithmeticExpression::initialize_hashmap_for_expression(&mut b);
                ArithmeticExpression::initialize_hashmap_for_expression(&mut c);
                ArithmeticExpression::add_symbol_to_coefficients(
                    symbol_0,
                    &BigInt::from(1),
                    &mut a,
                    field,
                );
                ArithmeticExpression::add_symbol_to_coefficients(
                    symbol_1,
                    &BigInt::from(1),
                    &mut b,
                    field,
                );
                Quadratic { a, b, c }
            }
            (Signal { symbol }, Linear { coefficients })
            | (Linear { coefficients }, Signal { symbol }) => {
                let a = coefficients.clone();
                let mut b = HashMap::new();
                let mut c = HashMap::new();
                ArithmeticExpression::initialize_hashmap_for_expression(&mut b);
                ArithmeticExpression::initialize_hashmap_for_expression(&mut c);
                ArithmeticExpression::add_symbol_to_coefficients(
                    symbol,
                    &BigInt::from(1),
                    &mut b,
                    field,
                );
                Quadratic { a, b, c }
            }
            (Linear { coefficients: coefficients_0 }, Linear { coefficients: coefficients_1 }) => {
                let a = coefficients_0.clone();
                let b = coefficients_1.clone();
                let mut c = HashMap::new();
                ArithmeticExpression::initialize_hashmap_for_expression(&mut c);
                Quadratic { a, b, c }
            }
        }
    }
    pub fn sub(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        let minus_one = Number { value: BigInt::from(-1) };
        let step_one = ArithmeticExpression::mul(&minus_one, right, field);
        ArithmeticExpression::add(left, &step_one, field)
    }

    pub fn div(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> Result<ArithmeticExpression<C>, ArithmeticError> {
        use ArithmeticExpression::*;
        match (left, right) {
            (Number { value: value_0 }, Number { value: value_1 }) => {
                let value = modular_arithmetic::div(value_0, value_1, field)?;
                Result::Ok(Number { value })
            }
            (Signal { symbol }, Number { value }) => {
                let mut coefficients = HashMap::new();
                ArithmeticExpression::initialize_hashmap_for_expression(&mut coefficients);
                ArithmeticExpression::add_symbol_to_coefficients(
                    symbol,
                    &BigInt::from(1),
                    &mut coefficients,
                    field,
                );
                ArithmeticExpression::divide_coefficients_by_constant(
                    value,
                    &mut coefficients,
                    field,
                )?;
                Result::Ok(Linear { coefficients })
            }
            (Linear { coefficients }, Number { value }) => {
                let mut coefficients = coefficients.clone();
                ArithmeticExpression::divide_coefficients_by_constant(
                    value,
                    &mut coefficients,
                    field,
                )?;
                Result::Ok(Linear { coefficients })
            }
            (Quadratic { a, b, c }, Number { value }) => {
                let mut a = a.clone();
                let mut b = b.clone();
                let mut c = c.clone();
                ArithmeticExpression::divide_coefficients_by_constant(value, &mut a, field)?;
                ArithmeticExpression::divide_coefficients_by_constant(value, &mut b, field)?;
                ArithmeticExpression::divide_coefficients_by_constant(value, &mut c, field)?;
                Result::Ok(Quadratic { a, b, c })
            }
            _ => Result::Ok(NonQuadratic),
        }
    }
    pub fn idiv(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> Result<ArithmeticExpression<C>, ArithmeticError> {
        use ArithmeticExpression::*;
        match (left, right) {
            (Number { value: value_0 }, Number { value: value_1 }) => {
                let value = modular_arithmetic::idiv(value_0, value_1, field)?;
                Result::Ok(Number { value })
            }
            (Signal { symbol }, Number { value }) => {
                let mut coefficients = HashMap::new();
                ArithmeticExpression::initialize_hashmap_for_expression(&mut coefficients);
                ArithmeticExpression::add_symbol_to_coefficients(
                    symbol,
                    &BigInt::from(1),
                    &mut coefficients,
                    field,
                );
                ArithmeticExpression::idivide_coefficients_by_constant(
                    value,
                    &mut coefficients,
                    field,
                )?;
                Result::Ok(Linear { coefficients })
            }
            (Linear { coefficients }, Number { value }) => {
                let mut coefficients = coefficients.clone();
                ArithmeticExpression::idivide_coefficients_by_constant(
                    value,
                    &mut coefficients,
                    field,
                )?;
                Result::Ok(Linear { coefficients })
            }
            (Quadratic { a, b, c }, Number { value }) => {
                let mut a = a.clone();
                let mut b = b.clone();
                let mut c = c.clone();
                ArithmeticExpression::idivide_coefficients_by_constant(value, &mut a, field)?;
                ArithmeticExpression::idivide_coefficients_by_constant(value, &mut b, field)?;
                ArithmeticExpression::idivide_coefficients_by_constant(value, &mut c, field)?;
                Result::Ok(Quadratic { a, b, c })
            }
            _ => Result::Ok(NonQuadratic),
        }
    }
    pub fn mod_op(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> Result<ArithmeticExpression<C>, ArithmeticError> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let value = modular_arithmetic::mod_op(value_0, value_1, field)?;
            Result::Ok(Number { value })
        } else {
            Result::Ok(NonQuadratic)
        }
    }
    pub fn pow(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        match (left, right) {
            (Number { value: value_0 }, Number { value: value_1 }) => {
                let value = modular_arithmetic::pow(value_0, value_1, field);
                Number { value }
            }
            (Signal { symbol }, Number { value }) => {
                if *value == BigInt::from(2) {
                    let left = Signal { symbol: symbol.clone() };
                    let right = Signal { symbol: symbol.clone() };
                    ArithmeticExpression::mul(&left, &right, field)
                } else {
                    NonQuadratic
                }
            }
            _ => NonQuadratic,
        }
    }
    pub fn prefix_sub(elem: &ArithmeticExpression<C>, field: &BigInt) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        let minus_one = Number { value: BigInt::from(-1) };
        ArithmeticExpression::mul(elem, &minus_one, field)
    }

    // Bit operations
    pub fn complement_256(
        elem: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        if let Number { value } = elem {
            Number { value: modular_arithmetic::complement_256(value, field) }
        } else {
            NonQuadratic
        }
    }
    pub fn shift_l(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> Result<ArithmeticExpression<C>, ArithmeticError> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let shifted_elem = modular_arithmetic::shift_l(value_0, value_1, field)?;
            Result::Ok(Number { value: shifted_elem })
        } else {
            Result::Ok(NonQuadratic)
        }
    }
    pub fn shift_r(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> Result<ArithmeticExpression<C>, ArithmeticError> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let shifted_elem = modular_arithmetic::shift_r(value_0, value_1, field)?;
            Result::Ok(Number { value: shifted_elem })
        } else {
            Result::Ok(NonQuadratic)
        }
    }
    pub fn bit_or(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let value = modular_arithmetic::bit_or(value_0, value_1, field);
            Number { value }
        } else {
            NonQuadratic
        }
    }
    pub fn bit_and(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let value = modular_arithmetic::bit_and(value_0, value_1, field);
            Number { value }
        } else {
            NonQuadratic
        }
    }
    pub fn bit_xor(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let value = modular_arithmetic::bit_xor(value_0, value_1, field);
            Number { value }
        } else {
            NonQuadratic
        }
    }

    // Boolean operations
    pub fn get_boolean_equivalence(elem: &ArithmeticExpression<C>, field: &BigInt) -> Option<bool> {
        use ArithmeticExpression::*;
        if let Number { value } = elem {
            Option::Some(modular_arithmetic::as_bool(value, field))
        } else {
            Option::None
        }
    }
    pub fn not(elem: &ArithmeticExpression<C>, field: &BigInt) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        if let Number { value } = elem {
            let value = modular_arithmetic::not(value, field);
            Number { value }
        } else {
            NonQuadratic
        }
    }
    pub fn bool_or(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let value = modular_arithmetic::bool_or(value_0, value_1, field);
            Number { value }
        } else {
            NonQuadratic
        }
    }
    pub fn bool_and(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let value = modular_arithmetic::bool_and(value_0, value_1, field);
            Number { value }
        } else {
            NonQuadratic
        }
    }
    pub fn eq(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let value = modular_arithmetic::eq(value_0, value_1, field);
            Number { value }
        } else {
            NonQuadratic
        }
    }
    pub fn not_eq(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let value = modular_arithmetic::not_eq(value_0, value_1, field);
            Number { value }
        } else {
            NonQuadratic
        }
    }
    pub fn lesser(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let value = modular_arithmetic::lesser(value_0, value_1, field);
            Number { value }
        } else {
            NonQuadratic
        }
    }
    pub fn lesser_eq(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let value = modular_arithmetic::lesser_eq(value_0, value_1, field);
            Number { value }
        } else {
            NonQuadratic
        }
    }
    pub fn greater(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let value = modular_arithmetic::greater(value_0, value_1, field);
            Number { value }
        } else {
            NonQuadratic
        }
    }
    pub fn greater_eq(
        left: &ArithmeticExpression<C>,
        right: &ArithmeticExpression<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        use ArithmeticExpression::*;
        if let (Number { value: value_0 }, Number { value: value_1 }) = (left, right) {
            let value = modular_arithmetic::greater_eq(value_0, value_1, field);
            Number { value }
        } else {
            NonQuadratic
        }
    }

    // Utils
    pub fn apply_substitutions(
        expr: &mut ArithmeticExpression<C>,
        substitution: &Substitution<C>,
        field: &BigInt,
    ) {
        use ArithmeticExpression::*;
        match expr {
            Linear { coefficients } => raw_substitution(coefficients, substitution, field),
            Signal { symbol } if *symbol == substitution.from => {
                *expr = Linear { coefficients: substitution.to.clone() };
            }
            Quadratic { a, b, c } => {
                raw_substitution(a, substitution, field);
                raw_substitution(b, substitution, field);
                raw_substitution(c, substitution, field);
            }
            _ => {}
        }
    }
    pub fn get_usize(expr: &ArithmeticExpression<C>) -> Option<usize> {
        use ArithmeticExpression::*;
        if let Number { value } = expr {
            value.to_usize()
        } else {
            Option::None
        }
    }
    pub fn is_number(&self) -> bool {
        matches!(self, ArithmeticExpression::Number { .. })
    }
    pub fn is_nonquadratic(&self) -> bool {
        matches!(self, ArithmeticExpression::NonQuadratic)
    }
    pub fn is_quadratic(&self) -> bool {
        matches!(self, ArithmeticExpression::Quadratic { .. })
    }
    pub fn is_linear(&self) -> bool {
        matches!(self, ArithmeticExpression::Linear { .. })
    }


}

// ******************************** Constraint Definition ********************************

/*
    Wrapper for linear expression that will be used as a substitution
*/

#[derive(Clone)]
pub struct Substitution<C>
where
    C: Hash + Eq,
{
    pub(crate) from: C,
    pub(crate) to: HashMap<C, BigInt>,
}
impl<C: Default + Clone + Display + Hash + Eq> Substitution<C> {
    // Substitution public utils
    pub fn new(from: C, to: ArithmeticExpression<C>) -> Option<Substitution<C>> {
        use ArithmeticExpression::*;
        match to {
            Number { value } => {
                let mut to = HashMap::new();
                to.insert(ArithmeticExpression::constant_coefficient(), value);
                Option::Some(Substitution { from, to })
            }
            Signal { symbol } => {
                let mut to = HashMap::new();
                to.insert(symbol, BigInt::from(1));
                Option::Some(Substitution { from, to })
            }
            Linear { coefficients: to } if !to.contains_key(&from) => {
                Option::Some(Substitution { from, to })
            }
            _ => Option::None,
        }
    }

    pub fn apply_correspondence_and_drop<K>(
        substitution: Substitution<C>,
        symbol_correspondence: &HashMap<C, K>,
    ) -> Substitution<K>
    where
        K: Default + Clone + Display + Hash + Eq,
    {
        Substitution::apply_correspondence(&substitution, symbol_correspondence)
    }

    pub fn constant_coefficient() -> C {
        ArithmeticExpression::constant_coefficient()
    }

    pub fn apply_correspondence<K>(
        substitution: &Substitution<C>,
        symbol_correspondence: &HashMap<C, K>,
    ) -> Substitution<K>
    where
        K: Default + Clone + Display + Hash + Eq,
    {
        let from = symbol_correspondence.get(&substitution.from).unwrap().clone();
        let to = apply_raw_correspondence(&substitution.to, symbol_correspondence);
        Substitution { to, from }
    }

    pub fn apply_substitution(src: &mut Substitution<C>, change: &Substitution<C>, field: &BigInt) {
        raw_substitution(&mut src.to, change, field);
    }

    pub fn substitution_into_constraint(
        substitution: Substitution<C>,
        field: &BigInt,
    ) -> Constraint<C> {
        let symbol = substitution.from;
        let mut coefficients = substitution.to;
        ArithmeticExpression::initialize_hashmap_for_expression(&mut coefficients);
        coefficients.insert(symbol, BigInt::from(1));
        let arith = ArithmeticExpression::Linear { coefficients };
        ArithmeticExpression::transform_expression_to_constraint_form(arith, field).unwrap()
    }

    pub fn decompose(substitution: Substitution<C>) -> (C, ArithmeticExpression<C>) {
        let c: C = ArithmeticExpression::constant_coefficient();
        let mut to = substitution.to;
        let right = if HashMap::len(&to) == 1 && HashMap::contains_key(&to, &c) {
            let value = HashMap::remove(&mut to, &c).unwrap();
            ArithmeticExpression::Number { value }
        } else if HashMap::len(&to) == 1 {
            let mut values: Vec<_> = to.values().cloned().collect();
            let mut symbols: Vec<_> = to.keys().cloned().collect();
            let symbol = symbols.pop().unwrap();
            let value = values.pop().unwrap();
            if value == BigInt::from(1) {
                ArithmeticExpression::Signal { symbol }
            } else {
                ArithmeticExpression::initialize_hashmap_for_expression(&mut to);
                ArithmeticExpression::Linear { coefficients: to }
            }
        } else {
            ArithmeticExpression::initialize_hashmap_for_expression(&mut to);
            ArithmeticExpression::Linear { coefficients: to }
        };
        (substitution.from, right)
    }

    pub fn map_into_arith_expr(
        substitution: Substitution<C>,
        field: &BigInt,
    ) -> ArithmeticExpression<C> {
        let (left, right) = Substitution::decompose(substitution);
        let left = ArithmeticExpression::Signal { symbol: left };
        ArithmeticExpression::sub(&right, &left, field)
    }

    pub fn from(&self) -> &C {
        &self.from
    }

    pub fn to(&self) -> &HashMap<C, BigInt> {
        &self.to
    }

    pub fn take_cloned_signals(&self) -> HashSet<C> {
        let cq: C = ArithmeticExpression::constant_coefficient();
        let mut signals = HashSet::new();
        for s in self.to.keys() {
            if cq != *s {
                signals.insert(s.clone());
            }
        }
        signals
    }
    

    pub fn take_signals(&self) -> HashSet<&C> {
        let cq: C = ArithmeticExpression::constant_coefficient();
        let mut signals = HashSet::new();
        for s in self.to.keys() {
            if cq != *s {
                signals.insert(s);
            }
        }
        signals
    }

    pub fn rmv_zero_coefficients(substitution: &mut Substitution<C>) {
        substitution.to = remove_zero_value_coefficients(std::mem::take(&mut substitution.to))
    }
}

impl Substitution<usize> {
    pub fn apply_offset(&self, offset: usize) -> Substitution<usize> {
        let constant: usize = Substitution::constant_coefficient();
        debug_assert_ne!(self.from, constant);
        let from = self.from + offset;
        let to = apply_raw_offset(&self.to, offset);
        Substitution { from, to }
    }
}

/*
    Represents a constraint of the form: A*B - C = 0
    where A,B and C are linear expression.
*/
#[derive(Clone)]
pub struct Constraint<C>
where
    C: Hash + Eq,
{
    pub(crate) a: HashMap<C, BigInt>,
    pub(crate) b: HashMap<C, BigInt>,
    pub(crate) c: HashMap<C, BigInt>,
}

impl<C: Default + Clone + Display + Hash + Eq> Constraint<C> {
    pub fn new(a: HashMap<C, BigInt>, b: HashMap<C, BigInt>, c: HashMap<C, BigInt>) -> Constraint<C> {
        Constraint { a, b, c }
    }

    pub fn empty() -> Constraint<C> {
        Constraint::new(
            HashMap::with_capacity(0),
            HashMap::with_capacity(0),
            HashMap::with_capacity(0),
        )
    }

    pub fn constant_coefficient() -> C {
        ArithmeticExpression::constant_coefficient()
    }
    pub fn apply_correspondence_and_drop<K>(
        constraint: Constraint<C>,
        symbol_correspondence: &HashMap<C, K>,
    ) -> Constraint<K>
    where
        K: Default + Clone + Display + Hash + Eq,
    {
        Constraint::apply_correspondence(&constraint, symbol_correspondence)
    }

    pub fn apply_correspondence<K>(
        constraint: &Constraint<C>,
        symbol_correspondence: &HashMap<C, K>,
    ) -> Constraint<K>
    where
        K: Default + Clone + Display + Hash + Eq,
    {
        let a = apply_raw_correspondence(&constraint.a, symbol_correspondence);
        let b = apply_raw_correspondence(&constraint.b, symbol_correspondence);
        let c = apply_raw_correspondence(&constraint.c, symbol_correspondence);
        Constraint::new(a, b, c)
    }

    // Constraint simplifications

    pub fn is_linear(constraint: &Constraint<C>) -> bool {
        constraint.a.is_empty() && constraint.b.is_empty()
    }

    pub fn clear_signal_from_linear(
        constraint: Constraint<C>,
        signal: &C,
        field: &BigInt,
    ) -> Substitution<C> {
        debug_assert!(Constraint::is_linear(&constraint));
        debug_assert!(constraint.c.contains_key(signal));
        let raw_expression = Constraint::clear_signal(constraint.c, &signal, field);
        Substitution { from: signal.clone(), to: raw_expression }
    }

    pub fn take_cloned_signals(&self) -> HashSet<C> {
        let mut signals = HashSet::new();
        for signal in self.a().keys() {
            signals.insert(signal.clone());
        }
        for signal in self.b().keys() {
            signals.insert(signal.clone());
        }
        for signal in self.c().keys() {
            signals.insert(signal.clone());
        }
        signals.remove(&Constraint::constant_coefficient());
        signals
    }

    pub fn take_signals_quadratic_equality(&self) -> (C, C, C) 
    where C: Copy
    {
        let signals_a: Vec<C> = self.a.keys().cloned().collect();
        let signals_b: Vec<C> = self.b.keys().cloned().collect();
        let signals_c: Vec<C> = self.c.keys().cloned().collect();
        (signals_a[0], signals_b[0], signals_c[0])
    }

    pub fn take_possible_cloned_monomials(&self) -> HashSet<(C, C)>
    where C: PartialOrd
     {
        let mut monomials = HashSet::new();

        for signal_a in self.a().keys() {
            for signal_b in self.b().keys() {
                if signal_a < signal_b {
                    monomials.insert((signal_a.clone(), signal_b.clone()));
                }
                else{
                    monomials.insert((signal_b.clone(), signal_a.clone()));
                }
            }
        }
        monomials
    }

    pub fn take_possible_cloned_strict_monomials(&self, field: &BigInt) -> HashSet<(C, C)>
    where C: PartialOrd + Copy
     {
        let mut monomials = HashSet::new();
        let mut appears_twice = LinkedList::new();

        for signal_a in self.a().keys() {
            for signal_b in self.b().keys() {
                if signal_a < signal_b {
                    if monomials.contains(&(*signal_a, *signal_b)){
                        appears_twice.push_back((signal_a, signal_b));
                    }
                    else{
                        monomials.insert((signal_a.clone(), signal_b.clone()));
                    }
                }
                else{
                    if monomials.contains(&(*signal_b, *signal_a)){
                        appears_twice.push_back((signal_b, signal_a));
                    }
                    else{
                        monomials.insert((signal_b.clone(), signal_a.clone()));
                    }
                }
            }
        }
        //println!("Tamaño de repetidas {}", appears_twice.len());
        for (signal_a, signal_b) in appears_twice{
            let coef_1 = modular_arithmetic::mul(self.a().get(signal_a).unwrap(), self.b().get(signal_a).unwrap(), field);
            let coef_2 = modular_arithmetic::mul(self.a().get(signal_b).unwrap(), self.b().get(signal_a).unwrap(), field);
            let value = modular_arithmetic::add(&coef_1, &coef_2, field);
            if value == BigInt::zero(){
                monomials.remove(&(*signal_a, *signal_b));
            }
        }

        monomials
    }


    pub fn take_cloned_monomials(&self, field: &BigInt) -> LinkedList<((C, C), BigInt)>
    where C: PartialOrd + Copy
     {

        let mut monomials = LinkedList::new();
        let mut map_monomials: HashMap<(C, C), BigInt> = HashMap::new();


        for (signal_a, coef_a) in self.a(){
            for (signal_b, coef_b) in self.b(){
                let new_coef = modular_arithmetic::mul(coef_a, coef_b, field);
                let monomial;
                if *signal_a < *signal_b {
                    monomial = (*signal_a, *signal_b);
                }
                else{
                    monomial = (*signal_b, *signal_a);
                }
                match map_monomials.get(&monomial){
                    Some(coef) =>{
                        let total_coef = modular_arithmetic::add(&new_coef, &coef, field);
                        map_monomials.insert(monomial, total_coef);
                    },
                    None =>{
                        map_monomials.insert(monomial, new_coef);
                    }
                }
            }
        }

        for (monomial, coef) in map_monomials{
            if coef != BigInt::zero(){
                monomials.push_back((monomial, coef));
            }
        }

        monomials
    }
    
    pub fn get_value_monomial(&self, monomial: (C, C), field: &BigInt) -> BigInt{
        let mut coef = BigInt::zero();

        match self.a().get(&monomial.0){
            Some(coef_a) =>{
                match self.b().get(&monomial.1){
                    Some(coef_b) =>{
                        let new_coef = modular_arithmetic::mul(coef_a, coef_b, field);
                        coef = modular_arithmetic::add(&new_coef, &coef, field);
                    },
                    None =>{},
                }
            },
            None =>{},
        }

        match self.a().get(&monomial.1){
            Some(coef_a) =>{
                match self.b().get(&monomial.0){
                    Some(coef_b) =>{
                        let new_coef = modular_arithmetic::mul(coef_a, coef_b, field);
                        coef = modular_arithmetic::add(&new_coef, &coef, field);
                    },
                    None =>{},
                }
            },
            None =>{},
        }
        coef
    }


    pub fn take_signals(&self) -> HashSet<&C> {
        let cc: C = Constraint::constant_coefficient();
        let mut signals = HashSet::new();
        for signal in self.a().keys() {
            signals.insert(signal);
        }
        for signal in self.b().keys() {
            signals.insert(signal);
        }
        for signal in self.c().keys() {
            signals.insert(signal);
        }
        HashSet::remove(&mut signals, &cc);
        signals
    }

    fn clear_signal(
        mut symbols: HashMap<C, BigInt>,
        key: &C,
        field: &BigInt,
    ) -> HashMap<C, BigInt> {
        let key_value = symbols.remove(&key).unwrap();
        assert!(!key_value.is_zero());
        let value_to_the_right = modular_arithmetic::mul(&key_value, &BigInt::from(-1), field);
        ArithmeticExpression::initialize_hashmap_for_expression(&mut symbols);
        let arithmetic_result = ArithmeticExpression::divide_coefficients_by_constant(
            &value_to_the_right,
            &mut symbols,
            field,
        );
        assert!(arithmetic_result.is_ok());
        remove_zero_value_coefficients(symbols)
    }

    pub fn apply_substitution(
        constraint: &mut Constraint<C>,
        substitution: &Substitution<C>,
        field: &BigInt,
    ) {
        raw_substitution(&mut constraint.a, substitution, field);
        raw_substitution(&mut constraint.b, substitution, field);
        raw_substitution(&mut constraint.c, substitution, field);
        Constraint::fix_constraint(constraint, field);
    }

    pub fn apply_substitution_normalize(
        constraint: &mut Constraint<C>,
        substitution: &Substitution<C>,
        field: &BigInt,
    ) {
        raw_substitution(&mut constraint.a, substitution, field);
        raw_substitution(&mut constraint.b, substitution, field);
        raw_substitution(&mut constraint.c, substitution, field);
        Constraint::fix_normalize_constraint(constraint, field);
    }

    pub fn remove_zero_value_coefficients(constraint: &mut Constraint<C>) {
        constraint.a = remove_zero_value_coefficients(std::mem::take(&mut constraint.a));
        constraint.b = remove_zero_value_coefficients(std::mem::take(&mut constraint.b));
        constraint.c = remove_zero_value_coefficients(std::mem::take(&mut constraint.c));
    }

    pub fn fix_constraint(constraint: &mut Constraint<C>, field: &BigInt) {
        fix_raw_constraint(&mut constraint.a, &mut constraint.b, &mut constraint.c, field);
    }

    pub fn fix_normalize_constraint(constraint: &mut Constraint<C>, field: &BigInt) {
        fix_normalize_raw_constraint(&mut constraint.a, &mut constraint.b, &mut constraint.c, field);
    }

    pub fn is_empty(&self) -> bool {
        self.a.is_empty() && self.b.is_empty() && self.c.is_empty()
    }

    pub fn has_constant_coefficient(&self) -> bool {
        self.a.contains_key(&Constraint::constant_coefficient())
            || self.b.contains_key(&Constraint::constant_coefficient())
            || self.a.contains_key(&Constraint::constant_coefficient())
    }

    pub fn a(&self) -> &HashMap<C, BigInt> {
        &self.a
    }
    pub fn b(&self) -> &HashMap<C, BigInt> {
        &self.b
    }

    pub fn c(&self) -> &HashMap<C, BigInt> {
        &self.c
    }
    

    pub fn is_equality(&self, field: &BigInt) -> bool {
        signal_equals_signal(&self.a, &self.b, &self.c, field)
    }

    pub fn is_constant_equality(&self) -> bool {
        signal_equals_constant(&self.a, &self.b, &self.c)
    }

    pub fn is_quadratic_equality(&self) -> bool {
        signal_equals_quadratic_equality(&self.a, &self.b, &self.c)
    }

    pub fn into_arithmetic_expressions(self) -> (ArithmeticExpression<C>, ArithmeticExpression<C>, ArithmeticExpression<C>) {
        (
            ArithmeticExpression::Linear { coefficients: self.a },
            ArithmeticExpression::Linear { coefficients: self.b },
            ArithmeticExpression::Linear { coefficients: self.c }
        )
    }

    pub fn destruct(self) -> (HashMap<C, BigInt>, HashMap<C, BigInt>, HashMap<C, BigInt>) {
        (
            self.a , self.b, self.c
        )
    }

    pub fn get_hash_constraint(constraint: &Constraint<usize>, field: &BigInt) -> HashConstraint{
        let norm_constraint = normalize(constraint.clone(), field);
        (get_hash(norm_constraint.a()), get_hash(norm_constraint.b()), get_hash(norm_constraint.c()))
    }

}

impl Constraint<usize> {
    pub fn apply_offset(&self, offset: usize) -> Constraint<usize> {
        let a = apply_raw_offset(&self.a, offset);
        let b = apply_raw_offset(&self.b, offset);
        let c = apply_raw_offset(&self.c, offset);
        Constraint::new(a, b, c)
    }
    pub fn apply_witness(&self, witness: &Vec<usize>) -> Constraint<usize> {
        let a = apply_vectored_correspondence(&self.a, witness);
        let b = apply_vectored_correspondence(&self.b, witness);
        let c = apply_vectored_correspondence(&self.c, witness);
        Constraint::new(a, b, c)
    }
}



// model utils
type RawExpr<C> = HashMap<C, BigInt>;

fn apply_vectored_correspondence(
    symbols: &HashMap<usize, BigInt>,
    map: &Vec<usize>,
) -> HashMap<usize, BigInt> {
    let mut mapped = HashMap::new();
    for (s, v) in symbols {
        mapped.insert(map[*s], v.clone());
    }
    mapped
}

fn apply_raw_correspondence<C, K>(
    symbols: &HashMap<C, BigInt>,
    map: &HashMap<C, K>,
) -> HashMap<K, BigInt>
where
    K: Default + Clone + Display + Hash + Eq,
    C: Default + Clone + Display + Hash + Eq,
{
    let constant_coefficient: C = ArithmeticExpression::constant_coefficient();
    let mut coefficients_as_correspondence = HashMap::new();
    for (key, value) in symbols {
        let id = if key.eq(&constant_coefficient) {
            ArithmeticExpression::constant_coefficient()
        } else {
            map.get(&key).expect(&format!("Unknown signal: {}", key)).clone()
        };
        coefficients_as_correspondence.insert(id, value.clone());
    }
    coefficients_as_correspondence
}

fn apply_raw_offset(h: &HashMap<usize, BigInt>, offset: usize) -> HashMap<usize, BigInt> {
    let mut new = HashMap::new();
    let constant: usize = Constraint::constant_coefficient();
    for (k, v) in h {
        if *k == constant {
            new.insert(*k, v.clone());
        } else {
            new.insert(*k + offset, v.clone());
        }
    }
    new
}

fn raw_substitution<C>(
    change: &mut HashMap<C, BigInt>,
    substitution: &Substitution<C>,
    field: &BigInt,
) where
    C: Default + Clone + Display + Hash + Eq,
{
    ArithmeticExpression::initialize_hashmap_for_expression(change);
    if let Option::Some(val) = change.remove(&substitution.from) {
        let mut coefficients = substitution.to.clone();
        ArithmeticExpression::initialize_hashmap_for_expression(&mut coefficients);
        ArithmeticExpression::multiply_coefficients_by_constant(&val, &mut coefficients, field);
        ArithmeticExpression::add_coefficients_to_coefficients(&coefficients, change, field);
    }
    *change = remove_zero_value_coefficients(std::mem::take(change));
}

fn remove_zero_value_coefficients<C>(raw_expression: HashMap<C, BigInt>) -> HashMap<C, BigInt>
where
    C: Default + Clone + Display + Hash + Eq,
{
    let mut clean_raw = HashMap::new();
    for (key, val) in raw_expression {
        if !val.is_zero() {
            clean_raw.insert(key, val);
        }
    }
    clean_raw
}

fn fix_raw_constraint<C>(a: &mut RawExpr<C>, b: &mut RawExpr<C>, c: &mut RawExpr<C>, field: &BigInt)
where
    C: Default + Clone + Display + Hash + Eq,
{
    *a = remove_zero_value_coefficients(std::mem::take(a));
    *b = remove_zero_value_coefficients(std::mem::take(b));
    *c = remove_zero_value_coefficients(std::mem::take(c));
    if HashMap::is_empty(a) || HashMap::is_empty(b) {
        HashMap::clear(a);
        HashMap::clear(b);
    } else if is_constant_expression(a) {
        constant_linear_linear_reduction(a, b, c, field);
    } else if is_constant_expression(b) {
        constant_linear_linear_reduction(b, a, c, field);
    }
}

fn fix_normalize_raw_constraint<C>(a: &mut RawExpr<C>, b: &mut RawExpr<C>, c: &mut RawExpr<C>, field: &BigInt)
where
    C: Default + Clone + Display + Hash + Eq,
{
    *a = remove_zero_value_coefficients(std::mem::take(a));
    *b = remove_zero_value_coefficients(std::mem::take(b));
    *c = remove_zero_value_coefficients(std::mem::take(c));
    if HashMap::is_empty(a) || HashMap::is_empty(b) {
        HashMap::clear(a);
        HashMap::clear(b);
    } else if is_constant_expression(a) {
        constant_linear_linear_reduction(a, b, c, field);
    } else if is_constant_expression(b) {
        constant_linear_linear_reduction(b, a, c, field);
    } else{
        constant_nonlinear_nonlinear_reduction(a, b, c, field);
    }
}

fn constant_linear_linear_reduction<C>(
    a: &mut RawExpr<C>,
    b: &mut RawExpr<C>,
    c: &mut RawExpr<C>,
    field: &BigInt,
) where
    C: Default + Clone + Display + Hash + Eq,
{
    let cq: C = ArithmeticExpression::constant_coefficient();
    ArithmeticExpression::initialize_hashmap_for_expression(c);
    ArithmeticExpression::initialize_hashmap_for_expression(b);
    let constant = HashMap::remove(a, &cq).unwrap();
    ArithmeticExpression::multiply_coefficients_by_constant(&constant, b, field);
    ArithmeticExpression::multiply_coefficients_by_constant(&BigInt::from(-1), b, field);
    ArithmeticExpression::add_coefficients_to_coefficients(b, c, field);
    *c = remove_zero_value_coefficients(std::mem::take(c));
    HashMap::clear(a);
    HashMap::clear(b);
}

fn constant_nonlinear_nonlinear_reduction<C>(
    a: &mut RawExpr<C>,
    b: &mut RawExpr<C>,
    c: &mut RawExpr<C>,
    field: &BigInt,
) where
    C: Default + Clone + Display + Hash + Eq,
{
    let cq: C = ArithmeticExpression::constant_coefficient();
    match HashMap::remove(a, &cq){
        Some(constant) =>{
            ArithmeticExpression::initialize_hashmap_for_expression(c);
            let mut aux_b: HashMap<C, BigInt> = b.clone();
            ArithmeticExpression::initialize_hashmap_for_expression(&mut aux_b);
            ArithmeticExpression::multiply_coefficients_by_constant(&constant, &mut aux_b, field);
            ArithmeticExpression::multiply_coefficients_by_constant(&BigInt::from(-1), &mut aux_b, field);
            ArithmeticExpression::add_coefficients_to_coefficients(&aux_b, c, field);

        },
        None => {},
    }
    match HashMap::remove(b, &cq){
        Some(constant) =>{
            ArithmeticExpression::initialize_hashmap_for_expression(c);
            let mut aux_a: HashMap<C, BigInt> = a.clone();
            ArithmeticExpression::initialize_hashmap_for_expression(&mut aux_a);
            ArithmeticExpression::multiply_coefficients_by_constant(&constant, &mut aux_a, field);
            ArithmeticExpression::multiply_coefficients_by_constant(&BigInt::from(-1), &mut aux_a, field);
            ArithmeticExpression::add_coefficients_to_coefficients(&aux_a, c, field);
        },
        _ =>{}, 

    }
    *c = remove_zero_value_coefficients(std::mem::take(c));
} 


fn signal_equals_signal<C>(a: &RawExpr<C>, b: &RawExpr<C>, c: &RawExpr<C>, field: &BigInt) -> bool
where
    C: Default + Clone + Display + Hash + Eq,
{
    let cq: C = ArithmeticExpression::constant_coefficient();
    if a.is_empty() && b.is_empty() && !HashMap::contains_key(c, &cq) && c.len() == 2 {
        let signals: Vec<_> = c.keys().cloned().collect();
        let c0 = HashMap::get(c, &signals[0]).unwrap();
        let c1 = HashMap::get(c, &signals[1]).unwrap();
        let c1_p = modular_arithmetic::mul(&BigInt::from(-1), c1, field);
        c1_p == *c0
    } else {
        false
    }
}

fn signal_equals_constant<C>(a: &RawExpr<C>, b: &RawExpr<C>, c: &RawExpr<C>) -> bool
where
    C: Default + Clone + Display + Hash + Eq,
{
    let cq: C = ArithmeticExpression::constant_coefficient();
    HashMap::is_empty(a)
        && HashMap::is_empty(b)
        && HashMap::contains_key(c, &cq)
        && HashMap::len(c) == 2
}

fn signal_equals_quadratic_equality<C>(a: &RawExpr<C>, b: &RawExpr<C>, c: &RawExpr<C>) -> bool
where
    C: Default + Clone + Display + Hash + Eq,
{
    let cq: C = ArithmeticExpression::constant_coefficient();
    HashMap::len(a) == 1
        && HashMap::len(b) == 1
        && !HashMap::contains_key(c, &cq)
        && HashMap::len(c) == 1
}

fn is_constant_expression<C>(expr: &RawExpr<C>) -> bool
where
    C: Default + Clone + Display + Hash + Eq,
{
    let cq: C = ArithmeticExpression::constant_coefficient();
    HashMap::contains_key(expr, &cq) && HashMap::len(expr) == 1
}

// Given a expression A and B and a coef coef, returns A + coef * B
pub fn add_linear_expression<C>(expr_a: &mut HashMap<C, BigInt>, expr_b: &mut HashMap<C, BigInt>, coef: &BigInt, field: &BigInt)
where
    C: Default + Clone + Display + Hash + Eq,
{

    ArithmeticExpression::initialize_hashmap_for_expression(expr_a);
    ArithmeticExpression::initialize_hashmap_for_expression(expr_b);
    ArithmeticExpression::multiply_coefficients_by_constant(coef, expr_b, field);
    ArithmeticExpression::add_coefficients_to_coefficients(
        expr_b,
        expr_a,
        field,
    );
    
}

pub fn get_linear_coefficients_ab(a: &mut HashMap<usize, BigInt>, b: &mut HashMap<usize, BigInt>, field: &BigInt) ->  HashMap<usize, BigInt>{

    let mut new_c: HashMap<usize, BigInt> = HashMap::with_capacity(0);
    let cq: usize = ArithmeticExpression::constant_coefficient();
    new_c.insert(cq, BigInt::from(0));

    if *a.get(&cq).unwrap() != BigInt::from(0){

        let value: &BigInt = a.get(&cq).unwrap();
        let mut aux_b_1: HashMap<usize, BigInt> = b.clone();
        ArithmeticExpression::multiply_coefficients_by_constant(&value, &mut aux_b_1, &field);
        ArithmeticExpression::add_coefficients_to_coefficients(&aux_b_1, &mut new_c, &field);
        a.insert(cq, BigInt::from(0));
    }
    if *b.get(&cq).unwrap() != BigInt::from(0){
        let value: &BigInt = b.get(&cq).unwrap();
        let mut aux_a_1: HashMap<usize, BigInt> = a.clone();
        ArithmeticExpression::multiply_coefficients_by_constant(&value, &mut aux_a_1, &field);
        ArithmeticExpression::add_coefficients_to_coefficients(&aux_a_1, &mut new_c, &field);
        b.insert(cq, BigInt::from(0));

    }
    new_c
}

pub fn get_coefficient_smallest_signal(a: &HashMap<usize, BigInt>) -> BigInt{
    let mut coefficient: BigInt = BigInt::from(0);
    let mut vector_aux: Vec<_> = a.iter().clone().collect();
    vector_aux.sort();
    let mut pos = 0;
    let mut found: bool = false;
    while pos < vector_aux.len() && !found{
        if *vector_aux[pos].1 != BigInt::from(0) {
            coefficient = vector_aux[pos].1.clone();
            found = true;
        }
        pos = pos + 1;
    }
    coefficient
}

pub fn is_zero_linear_expression(a: &HashMap<usize, BigInt>) -> bool{
    let first_coefficient: BigInt = get_coefficient_smallest_signal(a);
    first_coefficient == BigInt::from(0)
}

pub fn is_constant_linear_expression(a: &HashMap<usize, BigInt>) -> bool{
    let vector_aux: Vec<_> = a.iter().clone().collect();
    let mut pos = 0;
    let mut found: bool = false;
    while pos < vector_aux.len() && !found{
        if *vector_aux[pos].1 != BigInt::from(0) && *vector_aux[pos].0 != ArithmeticExpression::<usize>::constant_coefficient()
        {
            found = true;
        }
        pos = pos + 1;
    }
    !found
}


pub fn normalize(cons: Constraint<usize>, _field: &BigInt) -> Constraint<usize> {
    let mut new_constraint: Constraint<usize> = Constraint :: empty();

    let mut a: HashMap<_,_> = cons.a;
    let mut b: HashMap<_,_> = cons.b;
    let mut c: HashMap<_,_> = cons.c;

    ArithmeticExpression::initialize_hashmap_for_expression(&mut a);
    ArithmeticExpression::initialize_hashmap_for_expression(&mut b);
    ArithmeticExpression::initialize_hashmap_for_expression(&mut c);


    if is_zero_linear_expression(&a) || is_zero_linear_expression(&b){
        let first_coef_c: BigInt = get_coefficient_smallest_signal(&c);
        if first_coef_c != BigInt::from(0){
            ArithmeticExpression::divide_coefficients_by_constant(&first_coef_c, &mut c, &_field).unwrap();
            new_constraint.c = c;
        }
    }
    else if is_constant_linear_expression(&a) {

        let const_coef: &BigInt = a.get(&ArithmeticExpression::<usize>::constant_coefficient()).unwrap();
        ArithmeticExpression::multiply_coefficients_by_constant(&const_coef, &mut b, &_field);
        ArithmeticExpression::multiply_coefficients_by_constant(&BigInt::from(-1), &mut b, &_field);
        ArithmeticExpression::add_coefficients_to_coefficients(&b, &mut c, _field);
        let first_coef_c: BigInt = get_coefficient_smallest_signal(&c);
        if first_coef_c != BigInt::from(0){
            ArithmeticExpression::divide_coefficients_by_constant(&first_coef_c, &mut c, &_field).unwrap();
            new_constraint.c = c;
        }
    }
    else if is_constant_linear_expression(&b) {
        let const_coef: &BigInt = b.get(&ArithmeticExpression::<usize>::constant_coefficient()).unwrap();
        ArithmeticExpression::multiply_coefficients_by_constant(const_coef, &mut a, &_field);
        ArithmeticExpression::multiply_coefficients_by_constant(&BigInt::from(-1), &mut a, &_field);
        ArithmeticExpression::add_coefficients_to_coefficients(&a, &mut c, _field);
        let first_coef_c: BigInt = get_coefficient_smallest_signal(&c);
        if first_coef_c != BigInt::from(0){
            ArithmeticExpression::divide_coefficients_by_constant(&first_coef_c, &mut c, &_field).unwrap();
            new_constraint.c = c;
        }
    }
    else{
        let mut add_c : HashMap<usize, BigInt> = get_linear_coefficients_ab(&mut a, &mut b, &_field);
        ArithmeticExpression::multiply_coefficients_by_constant(&BigInt::from(-1), &mut add_c, &_field);
        ArithmeticExpression::add_coefficients_to_coefficients(&add_c, &mut c, _field);

        let mut keys_a: Vec<_> = a.keys().clone().collect();
        keys_a.sort();
        let mut keys_b: Vec<_> = b.keys().clone().collect();
        keys_b.sort();
        if keys_a >keys_b {
            let aux: HashMap<_,_> = a;
            a = b;
            b = aux; 
        }
           
        // We normalize dividing A and C by the first factor of A 
        let first_coef_a: BigInt = get_coefficient_smallest_signal(&a);
        ArithmeticExpression::divide_coefficients_by_constant(&first_coef_a, &mut a, &_field).unwrap();
        ArithmeticExpression::divide_coefficients_by_constant(&first_coef_a, &mut c, &_field).unwrap();
            
        // We normalize dividing B and C by the first factor of B
        let first_coef_b: BigInt = get_coefficient_smallest_signal(&b);
        ArithmeticExpression::divide_coefficients_by_constant(&first_coef_b, &mut b, &_field).unwrap();
        ArithmeticExpression::divide_coefficients_by_constant(&first_coef_b, &mut c, &_field).unwrap();

        new_constraint.a = a;
        new_constraint.b = b;
        new_constraint.c = c;

    }
    Constraint::remove_zero_value_coefficients(&mut new_constraint);
    new_constraint
}



pub type HashConstraint = (Vec<(usize, BigInt)>, Vec<(usize, BigInt)>, Vec<(usize, BigInt)>);


// TODO: Revisar si podemos evitar el clone
pub fn get_hash(expression: &HashMap<usize, BigInt>) -> Vec<(usize, BigInt)>{
    let mut vector_aux: Vec<(usize, BigInt)> = Vec::new();
    for (c, v) in expression{
        vector_aux.push((c.clone(), v.clone()));
    }
    vector_aux.sort();
    vector_aux
}



pub fn apply_substitution(expression:&mut HashMap<usize, BigInt>, substitution: &Substitution<usize>, field: &BigInt){
    raw_substitution(expression, substitution, field);
}

#[cfg(test)]
mod test {
    use crate::algebra::{ArithmeticExpression, Constraint, Substitution};
    use crate::modular_arithmetic;
    use num_bigint::BigInt;
    use std::collections::HashMap;
    const FIELD: &str = "257";
    type C = Constraint<usize>;
    type S = Substitution<usize>;
    type A = ArithmeticExpression<usize>;

    #[test]
    fn algebra_constraint_offset() {
        let offset = 7;
        let x = 1;
        let a = HashMap::new();
        let b = HashMap::new();
        let mut c = HashMap::new();
        c.insert(C::constant_coefficient(), BigInt::from(12));
        c.insert(x, BigInt::from(3));
        let constraint = C::new(a, b, c);
        let constraint_with_offset = constraint.apply_offset(offset);
        assert!(constraint_with_offset.a.is_empty());
        assert!(constraint_with_offset.b.is_empty());
        assert!(constraint_with_offset.c.contains_key(&C::constant_coefficient()));
        assert!(!constraint_with_offset.c.contains_key(&x));
        let new_x = x + offset;
        assert!(constraint_with_offset.c.contains_key(&new_x));
        let value = constraint_with_offset.c.get(&new_x).unwrap();
        assert!(value.eq(&BigInt::from(3)));
    }

    #[test]
    fn algebra_constraint_clear_signal() {
        let field = BigInt::parse_bytes(FIELD.as_bytes(), 10)
            .expect("generating the big int was not possible");
        let constant = C::constant_coefficient();
        let c_coefficient = BigInt::from(3);
        let x = 1;
        let x_coefficient = BigInt::from(1);
        let y = 2;
        let y_coefficient = BigInt::from(1);
        let a = HashMap::new();
        let b = HashMap::new();
        let mut c = HashMap::new();
        c.insert(x, x_coefficient);
        c.insert(y, y_coefficient);
        c.insert(constant, c_coefficient);
        // constraint: x + y + 3 = 0
        let constraint = C::new(a, b, c);
        // sub: x = -y -3  ==> x = 256*y + 254
        let sub = C::clear_signal_from_linear(constraint, &x, &field);
        assert_eq!(sub.from, x);
        let y_new_coefficient = modular_arithmetic::sub(&field, &BigInt::from(1), &field);
        let sub_value = sub.to.get(&y).unwrap();
        assert_eq!(*sub_value, y_new_coefficient);

        let constant_new_coefficient = BigInt::from(254);
        let sub_value = sub.to.get(&constant).unwrap();
        assert_eq!(*sub_value, constant_new_coefficient);
    }

    
    #[test]
    fn algebra_constraint_apply_substitution() {
        let field = BigInt::parse_bytes(FIELD.as_bytes(), 10)
            .expect("generating the big int was not possible");
        // symbols
        let x = 1;
        let y = 2;
        let constant = C::constant_coefficient();

        // constraint: x + y + 4 = 0
        let x_c = BigInt::from(1);
        let y_c = BigInt::from(1);
        let constant_c = BigInt::from(4);
        let a = HashMap::new();
        let b = HashMap::new();
        let mut c = HashMap::new();
        c.insert(x, x_c);
        c.insert(y, y_c);
        c.insert(constant, constant_c);
        let mut constraint = C::new(a, b, c);

        // substitution: x = 2y + 3
        let y_c = BigInt::from(2);
        let constant_c = BigInt::from(3);
        let from = x;
        let mut to_raw = HashMap::new();
        to_raw.insert(y, y_c);
        to_raw.insert(constant, constant_c);
        let to = A::Linear { coefficients: to_raw };
        let substitution = S::new(from, to).unwrap();

        // result: 3y + 7 = 0
        let expected_y_c = BigInt::from(3);
        let expected_constant_c = BigInt::from(7);
        C::apply_substitution(&mut constraint, &substitution, &field);
        let y_c = constraint.c.get(&y).unwrap();
        let constant_c = constraint.c.get(&constant).unwrap();
        assert!(constraint.a.is_empty());
        assert!(constraint.b.is_empty());
        assert_eq!(*y_c, expected_y_c);
        assert_eq!(*constant_c, expected_constant_c);
    }


    #[test]
    fn algebra_get_smallest_coefficient() {
        let field = BigInt::parse_bytes(FIELD.as_bytes(), 10)
            .expect("generating the big int was not possible");
        // symbols
        let x = 1;
        let y = 2;
        let constant = C::constant_coefficient();

        // expression: 3x + 3y + 6 = 0
        let x_c = BigInt::from(3);
        let y_c = BigInt::from(3);
        let constant_c = BigInt::from(6);
        let mut c = HashMap::new();
        c.insert(x, x_c);
        c.insert(y, y_c);
        c.insert(constant, constant_c);

        let expected_coef = BigInt::from(6);
        let coef = crate::algebra::get_coefficient_smallest_signal(&c);
        assert_eq!(coef, expected_coef);
    }


 
}
