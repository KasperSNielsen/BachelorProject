use hacspec_lib::*;


public_nat_mod!( //Custom Macro - defining a newtype with some functions - well defined macro's have library functions built in
    type_name: FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 6,
    modulo_value: "1d"
);

public_nat_mod!( //Custom Macro - defining a new type with some functions - well defined macro's have library functions built in
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 6,
    modulo_value: "20"
);
// p192 = 2^192 - 2^64 - 1
//16^48 - 16^16 - 1

type G1 = (FieldElement, FieldElement, bool);
type Fp2 = (FieldElement, FieldElement); //(12 + 8u)

fn fp2neg(n: Fp2) -> Fp2 {
    let (n1, n2) = n;
    (FieldElement::ZERO()-n1, FieldElement::ZERO()-n2)
}

fn fp2add(n: Fp2, m: Fp2) -> Fp2 { //Coordinate wise
    let (n1, n2) = n;
    let (m1, m2) = m;
    (n1 + m1, n2 + m2)
}

fn fp2mul(n: Fp2, m: Fp2) -> Fp2 { //Using u^2 = -1
    let (n1, n2) = n;
    let (m1, m2) = m;
    let x1 = n1 * m1 - (n2 * m2);
    let x2 = n1 * m2 + n2 * m1;
    (x1, x2)
}

fn fp2inv(n: Fp2) -> Fp2 {
    let (n1, n2) = n;
    let t0 = n1 * n1 - (n2 * n2);
    let t1 = t0.inv();
    let x1 = n1 * t1;
    let x2 = FieldElement::ZERO()-(n2 * t1);
    (x1, x2)

}



pub fn fieldfis() -> G1 {
    let zero = FieldElement::ZERO(); //Create element Zero from public_nat_mod macro called FieldElement
    let two = FieldElement::TWO(); // Same as above
    let maxval = FieldElement::max_val(); //Create max value, add 2, which would equal 1 under the mod
    (zero, two + maxval, false)
}


pub fn add(p: G1, q: G1) -> G1
{
    let mut resultpoint = (FieldElement::ZERO(), FieldElement::ZERO(), true); //G1 at infinity

    let (x_1, y_1, inf1) = p;
    let (x_2, y_2, inf2) = q;

    if inf1 {resultpoint = p;}
    else { if inf2 {resultpoint = q;}
    else { if y_1 != FieldElement::ZERO()-y_2 {
        let x_diff = x_2 - x_1; 
        let y_diff = y_2 - y_1;
        let xovery = y_diff * x_diff.inv(); //  x / y = x * y^-1
        let x_3 = xovery.exp(2u32) - x_1 - x_2;
        let y_3 = xovery * (x_1 - x_3) - y_1;
        resultpoint = (x_3, y_3, false);
    }}}
    resultpoint
}

pub fn double(p: G1, a: FieldElement) -> G1
{
    let mut resultpoint = (FieldElement::ZERO(), FieldElement::ZERO(), true); //G1 at infinity
    let (x_1, y_1, inf) = p;
    
    if !inf && y_1 != FieldElement::ZERO()
    {
        let x_12 = x_1.exp(2u32);
        let xovery = (FieldElement::from_literal(3u128) * x_12 + a) * (FieldElement::TWO() * y_1).inv();
        let x_3 = xovery.exp(2u32) - FieldElement::TWO()*x_1;
        let y_3 = xovery * (x_1 - x_3) - y_1;
        resultpoint = (x_3, y_3, false);    
    }

    resultpoint
}


//Returns index of left-most bit, set to 1
pub fn most_significant_bit(m: Scalar, n: usize) -> usize 
{
    let mut result = 0;
    if n == 0 {
        result = 0;
    } else {
        if m.bit(n) {
            result = n;
        } else {
            result = most_significant_bit(m, n-1);
        }
    }
    result
}

pub fn mult(m: Scalar, p: G1, a: FieldElement) -> G1
{
    let n = 6;
    let k = n - most_significant_bit(m, n);
    let mut t = p;
    for i in k..n { //starting from second most significant bit
        t = double(t, a);
        if m.bit(n-i-1) {
            t = add(t, p);
        }
    }
    t
}
/*
T <- P
T <- 2T
if m = 1 : T <- T + P

*/