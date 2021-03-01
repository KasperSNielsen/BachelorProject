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
    /*
    if n > 0 && !m.bit(n) {
        most_significant_bit(m, n-1)
    } else { n }    
    */
    
    let mut result = n;
    if n > 0 && !m.bit(n) {
        result = most_significant_bit(m, n-1);
    }
    result
    
}

type G1 = (Fp, Fp);
pub type Fp2 = (Fp, Fp); //(10, 8) = (10+8u) : u^2 = -1
type G2 = (Fp2, Fp2);
pub type Fp6 = (Fp2, Fp2, Fp2);
pub type Fp12 = (Fp6, Fp6);




/* Arithmetic for FP2 elements */
fn fp2zero() -> Fp2 {
    fp2fromfp(Fp::ZERO())
}

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

pub fn fp2sub(n: Fp2, m: Fp2) -> Fp2 {
    fp2add(n, fp2neg(m))
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

/* Arithmetic for Fp6 elements */
pub fn fp6fromfp2(n: Fp2) -> Fp6 {
    (n, fp2zero(), fp2zero())
}

fn fp6zero() -> Fp6 {
    fp6fromfp2(fp2zero())
}

pub fn fp6neg(n: Fp6) -> Fp6 {
    let (n1, n2, n3) = n;
    (fp2sub(fp2zero(), n1), fp2sub(fp2zero(), n2), fp2sub(fp2zero(), n3))
}

pub fn fp6add(n: Fp6, m: Fp6) -> Fp6 {
    let (n1, n2, n3) = n;
    let (m1, m2, m3) = m;
    (fp2add(n1, m1), fp2add(n2, m2), fp2add(n3, m3))
}

pub fn fp6sub(n: Fp6, m: Fp6) -> Fp6 {
    fp6add(n, fp6neg(m))
}

pub fn fp6mul(n: Fp6, m: Fp6) -> Fp6 {
    let (n1, n2, n3) = n;
    let (m1, m2, m3) = m;
    let eps = (Fp::ONE(), Fp::ONE()); //1 + u
    let t1 = fp2mul(n1, m1);
    let t2 = fp2mul(n2, m2);
    let t3 = fp2mul(n3, m3);
    let t4 = fp2mul(fp2add(n2, n3), fp2add(m2, m3)); // (n2 + n3) * (m2 + m3)
    let t5 = fp2sub(fp2sub(t4, t2), t3); //t4 - t2 - t3
    let x = fp2add(fp2mul(t5, eps), t1); // t5 * eps + t1
    
    let t4 = fp2mul(fp2add(n1, n2), fp2add(m1, m2)); //(n1 + n2) * (m1 + m2)
    let t5 = fp2sub(fp2sub(t4, t1), t2); //t4 - t1 - t2
    let y = fp2add(t5, fp2mul(eps, t3)); //t5 + (eps * t3)
     
    let t4 = fp2mul(fp2add(n1, n3), fp2add(m1, m3)); //(n1 + n3) * (m1 + m3)
    let t5 = fp2sub(fp2sub(t4, t1), t3); //t4 - t1 - t3
    let z = fp2add(t5, t2); //t5 + t2
    (x, y, z)
}

pub fn fp6inv(n: Fp6) -> Fp6 {
    let (n1, n2, n3) = n;
    let eps = (Fp::ONE(), Fp::ONE()); //1 + u
    let t1 = fp2mul(n1, n1); //n1^2
    let t2 = fp2mul(n2, n2); //n2^2
    let t3 = fp2mul(n3, n3); //n3^2
    let t4 = fp2mul(n1, n2); //n1 * n2
    let t5 = fp2mul(n1, n3); //n1 * n3
    let t6 = fp2mul(n2, n3); //n2 * n3
    let x0 = fp2sub(t1, fp2mul(eps, t6)); //t1 - (eps * t6)
    let y0 = fp2sub(fp2mul(eps, t3), t4); //(eps * t3) - t4
    let z0 = fp2sub(t2, t5); //t2 - t5
    let t0 = fp2mul(n1, x0); //n1 * x0
    let t0 = fp2add(t0, fp2mul(eps, fp2mul(n3, y0))); //t0 + (eps * n3 * y0)
    let t0 = fp2add(t0, fp2mul(eps, fp2mul(n2, z0))); //t0 + (eps * n2 * z0)
    let t0 = fp2inv(t0); //t0^-1
    let x = fp2mul(x0, t0); //x0 * t0
    let y = fp2mul(y0, t0); // y0 * t0
    let z = fp2mul(z0, t0); // z0 * t0
    (x, y, z)
    

}

/* Arithmetic for Fp12 elements */

pub fn fp12fromfp6(n: Fp6) -> Fp12 {
    (n, fp6zero())
}

pub fn fp12neg(n: Fp12) -> Fp12 {
    let (n1, n2) = n;
    (fp6sub(fp6zero(), n1), fp6sub(fp6zero(), n2))
}

pub fn fp12add(n: Fp12, m: Fp12) -> Fp12 {
    let (n1, n2) = n;
    let (m1, m2) = m;
    (fp6add(n1, m1), fp6add(n2, m2))
}

pub fn fp12sub(n: Fp12, m: Fp12) -> Fp12 {
    fp12add(n, fp12neg(m))
}

pub fn fp12mul(n: Fp12, m: Fp12) -> Fp12 {
    let (n1, n2) = n;
    let (m1, m2) = m;
    let gamma = (fp2zero(), fp2fromfp(Fp::ONE()), fp2zero()); //0 + v + 0 (c0, c1v, c2v^2)
    
    let t1 = fp6mul(n1, m1); //n1 * n2
    let t2 = fp6mul(n2, m2); //n2 * m2
    let x = fp6add(t1, fp6mul(t2, gamma)); //t1 + (t2 * gamma)
    let y = fp6mul(fp6add(n1, n2), fp6add(m1, m2)); //(n1 + n2) * (m1 + m2)
    let y = fp6sub(fp6sub(y, t1), t2); //y - t1 - t2
    (x, y)
}

pub fn fp12inv(n: Fp12) -> Fp12 {
    let (n1, n2) = n;
    let gamma = (fp2zero(), fp2fromfp(Fp::ONE()), fp2zero()); //0 + v + 0 (c0, c1v, c2v^2)
    
    let t1 = fp6mul(n1, n1); //n1^2
    let t2 = fp6mul(n2, n2); //n2^2
    let t1 = fp6sub(t1, fp6mul(gamma, t2)); //t1 - (gamma * t2)
    let t2 = fp6inv(t1); //t1^-1
    let x = fp6mul(n1, t2); //n1 * t2
    let y = fp6neg(fp6mul(n2, t2)); //-(n2 * t2)
    (x, y)
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

    let x_diff = fp2sub(x2, x1); 
    let y_diff = fp2sub(y2, y1); 
    let xovery = fp2mul(y_diff, fp2inv(x_diff)); //  x / y = x * y^-1
    let t1 = fp2mul(xovery, xovery);
    let t2 = fp2sub(t1, x1);
    let x3 = fp2sub(t2, x2); 
    let t1 = fp2sub(x1, x3); 
    let t2 = fp2mul(xovery, t1);
    let y3 = fp2sub(t2, y1); 
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
    let x3 = fp2sub(t1, t2);
    let t1 = fp2sub(x1, x3);
    let t2 = fp2mul(xovery, t1);
    let y3 = fp2sub(t2, y1);
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