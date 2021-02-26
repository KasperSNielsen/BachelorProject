// BLS: y^2 = x^3 + 4

use hacspec_lib::*;

public_nat_mod!( //Custom Macro - defining a newtype with some functions - well defined macro's have library functions built in
    type_name: Fp,
    type_of_canvas: FpCanvas,
    bit_size_of_field: 384, //381 with 3 extra bits
    modulo_value: "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab" //0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
);

bytes!(SerializedFp, 48); //Represent points as arrays for easier testing

public_nat_mod!( //Custom Macro - defining a new type with some functions - well defined macro's have library functions built in
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "8000000000000000000000000000000000000000000000000000000000000000" //0x8000000000000000000000000000000000000000000000000000000000000000
);

//Returns index of left-most bit, set to 1
fn most_significant_bit(m: Scalar, n: usize) -> usize 
{
    let mut result = 0; //Weird warning
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

type G1 = (Fp, Fp);
type Fp2 = (Fp, Fp); //(10, 8) = (10+8u) : u^2 = -1
type G2 = (Fp2, Fp2);

/* Arithmetic for FP2 elements */

pub fn fp2fromfp(n: Fp) -> Fp2 {
    (n, Fp::ZERO())
}

pub fn fp2neg(n: Fp2) -> Fp2 {
    let (n1, n2) = n;
    (Fp::ZERO()-n1, Fp::ZERO()-n2)
}

pub fn fp2add(n: Fp2, m: Fp2) -> Fp2 { //Coordinate wise
    let (n1, n2) = n;
    let (m1, m2) = m;
    (n1 + m1, n2 + m2)
}

pub fn fp2mul(n: Fp2, m: Fp2) -> Fp2 { //(a+bu)*(c+du) = ac + adu + bcu + bdu^2 = ac - bd + (ad + bc)u
    let (n1, n2) = n;
    let (m1, m2) = m;
    let x1 = (n1 * m1) - (n2 * m2);
    let x2 = (n1 * m2) + (n2 * m1);
    (x1, x2)
}


pub fn fp2inv(n: Fp2) -> Fp2 {
    let (n1, n2) = n;
    let t0 = n1 * n1 + (n2 * n2);
    let t1 = t0.inv();
    let x1 = n1 * t1;
    let x2 = Fp::ZERO() - (n2 * t1);
    (x1, x2)
}

/* Arithmetic in G1 */

pub fn g1add(p: G1, q: G1) -> G1
{
    let (x1, y1) = p;
    let (x2, y2) = q;

    let x_diff = x2 - x1; 
    let y_diff = y2 - y1;
    let xovery = y_diff * x_diff.inv(); //  x / y = x * y^-1
    let x3 = xovery.exp(2u32) - x1 - x2;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3)
}

pub fn g1double(p: G1) -> G1
{
    let (x1, y1) = p;
    
    let x12 = x1.exp(2u32);
    let xovery = (Fp::from_literal(3u128) * x12) * (Fp::TWO() * y1).inv();
    let x3 = xovery.exp(2u32) - Fp::TWO()*x1;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3)
}



pub fn g1mult(m: Scalar, p: G1) -> G1
{
    let n = 255;
    let k = n - most_significant_bit(m, n);
    let mut t = p;
    for i in k..n { //starting from second most significant bit
        t = g1double(t);
        if m.bit(n-i-1) {
            t = g1add(t, p);
        }
    }
    t
}

/* Arithmetic in G2 */

pub fn g2add(p: G2, q: G2) -> G2
{
    let (x1, y1) = p;
    let (x2, y2) = q;

    let x_diff = fp2add(x2, fp2neg(x1)); 
    let y_diff = fp2add(y2, fp2neg(y1)); 
    let xovery = fp2mul(y_diff, fp2inv(x_diff)); //  x / y = x * y^-1
    let t1 = fp2mul(xovery, xovery);
    let t2 = fp2add(t1, fp2neg(x1));
    let x3 = fp2add(t2, fp2neg(x2)); 
    let t1 = fp2add(x1, fp2neg(x3)); 
    let t2 = fp2mul(xovery, t1);
    let y3 = fp2add(t2, fp2neg(y1)); 
    (x3, y3)
}

pub fn g2double(p: G2) -> G2
{
    let (x1, y1) = p;
    
    let x12 = fp2mul(x1, x1);
    let t1 = fp2mul(fp2fromfp(Fp::from_literal(3u128)), x12);
    let t2 = fp2inv(fp2mul(fp2fromfp(Fp::TWO()), y1));    
    let xovery = fp2mul(t1, t2);
    let t1 = fp2mul(xovery, xovery);
    let t2 = fp2mul(fp2fromfp(Fp::TWO()), x1);
    let x3 = fp2add(t1, fp2neg(t2));
    let t1 = fp2add(x1, fp2neg(x3));
    let t2 = fp2mul(xovery, t1);
    let y3 = fp2add(t2, fp2neg(y1));
    (x3, y3)
}

pub fn g2mult(m: Scalar, p: G2) -> G2
{
    let n = 255;
    let k = n - most_significant_bit(m, n);
    let mut t = p;
    for i in k..n { //starting from second most significant bit
        t = g2double(t);
        if m.bit(n-i-1) {
            t = g2add(t, p);
        }
    }
    t
}