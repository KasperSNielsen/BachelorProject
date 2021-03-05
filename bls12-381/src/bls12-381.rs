// BLS: y^2 = x^3 + 4

use hacspec_lib::*;

public_nat_mod!( //Custom Macro - defining a newtype with some functions - well defined macro's have library functions built in
    type_name: Fp,
    type_of_canvas: FpCanvas,
    bit_size_of_field: 384, //381 with 3 extra bits
    modulo_value: "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab" //0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
);



bytes!(SerializedFp, 48); //Represent points as arrays for easier testing
array!(ArrayFp, 6, U64);
/*
public_nat_mod!( //Custom Macro - defining a new type with some functions - well defined macro's have library functions built in
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "8000000000000000000000000000000000000000000000000000000000000000" //0x8000000000000000000000000000000000000000000000000000000000000000
);
*/
public_nat_mod!( //Custom Macro - defining a new type with some functions - well defined macro's have library functions built in
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 384,
    modulo_value: "800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000" //0x8000000000000000000000000000000000000000000000000000000000000000
);

//Returns index of left-most bit, set to 1
pub fn most_significant_bit(m: Scalar, n: usize) -> usize 
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
//bool is "isPointAtInfinity"
pub type G1 = (Fp, Fp, bool);
pub type Fp2 = (Fp, Fp); //(10, 8) = (10+8u) : u^2 = -1
pub type G2 = (Fp2, Fp2, bool);
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

pub fn fp2conjugate(n: Fp2) -> Fp2 {
    let (n1, n2) = n;
    (n1, Fp::ZERO()-n2)
}

pub fn fp2exp(n: Fp2, k: Scalar) -> Fp2 {
    let l = 383 - most_significant_bit(k, 383);
    let mut c = n;
    for i in l..383 { //starting from second most significant bit
        c = fp2mul(c, c);
        if k.bit(383-i-1) {
            c = fp2mul(c, n);
        }
    }
    c
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

pub fn fp12exp(n: Fp12, k: Scalar) -> Fp12 {
    let l = 255 - most_significant_bit(k, 255);
    let mut c = n;
    for i in l..255 { //starting from second most significant bit
        c = fp12mul(c, c);
        if k.bit(255-i-1) {
            c = fp12mul(c, n);
        }
    }
    c
}

pub fn fp12conjugate(n: Fp12) -> Fp12 {
    let (n1, n2) = n;
    (n1, fp6neg(n2))
}

/* Arithmetic in G1 */

fn g1add_a(p: G1, q: G1) -> G1
{
    let (x1, y1, _) = p;
    let (x2, y2, _) = q;

    let x_diff = x2 - x1; 
    let y_diff = y2 - y1;
    let xovery = y_diff * x_diff.inv(); //  x / y = x * y^-1
    let x3 = xovery.exp(2u32) - x1 - x2;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3, false)
}

fn g1double_a(p: G1) -> G1
{
    let (x1, y1, _) = p;
    
    let x12 = x1.exp(2u32);
    let xovery = (Fp::from_literal(3u128) * x12) * (Fp::TWO() * y1).inv();
    let x3 = xovery.exp(2u32) - Fp::TWO()*x1;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3, false)
}
//Wrapper with Point of Infinity
pub fn g1add(p: G1, q: G1) -> G1 {
    let (x1, y1, inf1) = p;
    let (x2, y2, inf2) = q;

    let mut result = (Fp::ZERO(), Fp::ZERO(), true);
    if inf1 {
        result = q;
    } else { if inf2 {
        result = p;
    } else { if p == q {
        result = g1double_a(p);
    } else { if !(x1 == x2 && y1 == Fp::ZERO() - y2) {
        result = g1add_a(p, q);
    }}}}
    result
}

pub fn g1double(p: G1) -> G1 {
    let (_x1, y1, inf1) = p;
    let mut result = (Fp::ZERO(), Fp::ZERO(), true);
    if y1 != Fp::ZERO() && !inf1 {
        result = g1double_a(p);
    }
    result
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

fn g2add_a(p: G2, q: G2) -> G2
{
    let (x1, y1, _) = p;
    let (x2, y2, _) = q;

    let x_diff = fp2sub(x2, x1); 
    let y_diff = fp2sub(y2, y1); 
    let xovery = fp2mul(y_diff, fp2inv(x_diff)); //  x / y = x * y^-1
    let t1 = fp2mul(xovery, xovery);
    let t2 = fp2sub(t1, x1);
    let x3 = fp2sub(t2, x2); 
    let t1 = fp2sub(x1, x3); 
    let t2 = fp2mul(xovery, t1);
    let y3 = fp2sub(t2, y1); 
    (x3, y3, false)
}

fn g2double_a(p: G2) -> G2
{
    let (x1, y1, _) = p;
    
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
    (x3, y3, false)
}

//Wrapper with Point of Infinity
pub fn g2add(p: G2, q: G2) -> G2 {
    let (x1, y1, inf1) = p;
    let (x2, y2, inf2) = q;

    let mut result = (fp2zero(), fp2zero(), true);
    if inf1 {
        result = q;
    } else { if inf2 {
        result = p;
    } else { if p == q {
        result = g2double_a(p);
    } else { if !(x1 == x2 && y1 == fp2neg(y2)) {
        result = g2add_a(p, q);
    }}}}
    result
}

pub fn g2double(p: G2) -> G2 {
    let (_x1, y1, inf1) = p;
    let mut result = (fp2zero(), fp2zero(), true);
    if y1 != fp2zero() && !inf1 {
        result = g2double_a(p);
    }
    result
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
//To Do on the following couple of functions: Throw error if twisting point at infinity
pub fn twist(p: G1) -> (Fp12, Fp12) {
    let (p0, p1, _) = p;
    let x = ((fp2zero(), fp2fromfp(p0), fp2zero()) , fp6zero());
    let y = (fp6zero(), (fp2zero(), fp2fromfp(p1), fp2zero()));
    (x, y)
}

pub fn line_double_p(r: G2, p: G1) -> Fp12 {
    let (r0, r1, _) = r;
    let a = fp2mul(fp2fromfp(Fp::from_literal(3u128)), fp2mul(r0, r0));
    let a = fp2mul(a, fp2inv(fp2mul(fp2fromfp(Fp::TWO()), r1)));
    let b = fp2sub(r1, fp2mul(a, r0));
    let a = fp12fromfp6(fp6fromfp2(a));
    let b = fp12fromfp6(fp6fromfp2(b));
    let (x, y) = twist(p);
    fp12sub(fp12sub(y, fp12mul(a, x)), b) //y - ax - b
}

fn line_add_p(r: G2, q: G2, p: G1) -> Fp12 {
    let (r0, r1, _) = r;
    let (q0, q1, _) = q;
    let a = fp2mul(fp2sub(q1, r1), fp2inv(fp2sub(q0, r0)));
    let b = fp2sub(r1, fp2mul(a, r0));
    let a = fp12fromfp6(fp6fromfp2(a));
    let b = fp12fromfp6(fp6fromfp2(b));
    let (x, y) = twist(p);
    fp12sub(fp12sub(y, fp12mul(a, x)), b) //y - ax - b
}

pub fn frobenius(f: Fp12) -> Fp12 {
    let ((g0, g1, g2), (h0, h1, h2)) = f;
    let t1 = fp2conjugate(g0);
    let t2 = fp2conjugate(h0);
    let t3 = fp2conjugate(g1);
    let t4 = fp2conjugate(h1);
    let t5 = fp2conjugate(g2);
    let t6 = fp2conjugate(h2); 


    //Funky way of storing gamma11
            //1904D3BF02BB0667    C231BEB4202C0D1F  0FD603FD3CBD5F4F  7B2443D784BAB9C4    F67EA53D63E7813D   8D0775ED92235FB8
    let c1 = ArrayFp(secret_array!(
        U64,
        [0x8D0775ED92235FB8u64,
        0xF67EA53D63E7813Du64,
        0x7B2443D784BAB9C4u64,
        0x0FD603FD3CBD5F4Fu64,
        0xC231BEB4202C0D1Fu64,
        0x1904D3BF02BB0667u64]
    ));

    let c1 = ArrayFp::to_le_bytes(&c1);
    let c1 = Fp::from_byte_seq_le(c1);

            //00FC3E2B36C4E032 88E9E902231F9FB8 54A14787B6C7B36F EC0C8EC971F63C5F 282D5AC14D6C7EC2 2CF78A126DDC4AF3
    let c2 = ArrayFp(secret_array!(
        U64,
        [0x2CF78A126DDC4AF3u64,
        0x282D5AC14D6C7EC2u64,
        0xEC0C8EC971F63C5Fu64,
        0x54A14787B6C7B36Fu64,
        0x88E9E902231F9FB8u64,
        0x00FC3E2B36C4E032u64]
    ));
    

    let c2 = ArrayFp::to_le_bytes(&c2);
    let c2 = Fp::from_byte_seq_le(c2);
    
    // gamma11 = (1+u)^((p-1) / 6)
    let gamma11 = (c1, c2);
    let gamma12 = fp2exp(gamma11, Scalar::from_literal(2u128));
    let gamma13 = fp2exp(gamma11, Scalar::from_literal(3u128));
    let gamma14 = fp2exp(gamma11, Scalar::from_literal(4u128));
    let gamma15 = fp2exp(gamma11, Scalar::from_literal(5u128));

    let t2 = fp2mul(t2, gamma11);
    let t3 = fp2mul(t3, gamma12);
    let t4 = fp2mul(t4, gamma13);
    let t5 = fp2mul(t5, gamma14);
    let t6 = fp2mul(t6, gamma15);

    ((t1, t3, t5), (t2, t4, t6))
}

fn final_exponentiation(f: Fp12) -> Fp12 {
    let fp6 = fp12conjugate(f);
    let finv = fp12inv(f);
    let fp6_1 = fp12mul(fp6, finv);
    let fp8 = frobenius(frobenius(fp6_1));
    let f = fp12mul(fp8, fp6_1); // f = f^((p^6-1)(p^2+1))

    let u = Scalar::from_literal(0xd201000000010000u128);

    let t0 = fp12mul(f, f);
    let t1 = fp12exp(t0, u);
    let t2 = fp12exp(t1, u / Scalar::TWO());
    let t3 = fp12conjugate(f);
    let t1 = fp12mul(t3, t1);

    let t1 = fp12conjugate(t1);
    let t1 = fp12mul(t1, t2);

    let t2 = fp12exp(t1, u);

    let t3 = fp12exp(t2, u);
    let t1 = fp12conjugate(t1);
    let t3 = fp12mul(t1, t3);

    let t1 = fp12conjugate(t1);
    let t1 = frobenius(frobenius(frobenius(t1)));
    let t2 = frobenius(frobenius(t2));
    let t1 = fp12mul(t1, t2);
    
    let t2 = fp12exp(t3, u);
    let t2 = fp12mul(t2, t0);
    let t2 = fp12mul(t2, f);

    let t1 = fp12mul(t1, t2);
    let t2 = frobenius(t3);
    let t1 = fp12mul(t1, t2);
    t1
}

pub fn pairing(p: G1, q: G2) -> Fp12 {
    let t = Scalar::from_literal(0xd201000000010000u128); 
    let mut r = q;
    let mut f = fp12fromfp6(fp6fromfp2(fp2fromfp(Fp::ONE())));
    for i in 1..64 {
        let lrr = line_double_p(r, p);
        r = g2double(r);
        f = fp12mul(fp12mul(f, f), lrr);
        if t.bit(64 - i - 1) {
            let lrq = line_add_p(r, q, p);
            r = g2add(r, q);
            f = fp12mul(f, lrq);
        }
    }
    final_exponentiation(f)
}
