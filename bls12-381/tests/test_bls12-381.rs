/* TO DO: Property Tests with associativity and distributive law */


use bls12_381::*;
use hacspec_lib::*;

#[cfg(test)]
extern crate quickcheck;
use quickcheck::*;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

/* Property Based Testing features, needed to perform testing */

//Wrapper around Fp, so we can implement arbitrary
#[derive(Debug)]
#[derive(Clone)]
struct TestFp(Fp);
type TestFp2 = (TestFp, TestFp);
type TestFp6 = (TestFp2, TestFp2, TestFp2);
type TestFp12 = (TestFp6, TestFp6);
#[derive(Debug)]
#[derive(Clone)]
struct TestScalar(Scalar);

/* Arbitrary Implementation used for Property Based Tests */
#[cfg(test)]
impl Arbitrary for TestFp {
    fn arbitrary(g: &mut Gen) -> TestFp {
        let mut a: [u64; 6] = [0; 6];
        for i in 0..6 {
            a[i] = u64::arbitrary(g);
        }        
        let mut b: [u8; 48] = [0; 48];
        for i in 0..6 {
            let val: u64 = a[i];
            b[(i*8)..((i+1)*8)].copy_from_slice(&(val.to_le_bytes()));
        }
        TestFp(Fp::from_byte_seq_le(Seq::<U8>::from_public_slice(&b)))
    }
}
/* Arbitrary Implementation used for Property Based Tests */
#[cfg(test)]
impl Arbitrary for TestScalar {
    fn arbitrary(g: &mut Gen) -> TestScalar {
        let mut a: [u64; 4] = [0; 4];
        for i in 0..4 {
            a[i] = u64::arbitrary(g);
        }
        let mut b: [u8; 32] = [0; 32];
        for i in 0..4 {
            let val: u64 = a[i];
            b[(i*8)..((i+1)*8)].copy_from_slice(&(val.to_le_bytes()));
        }
        TestScalar(Scalar::from_byte_seq_le(Seq::<U8>::from_public_slice(&b)))
    }
}

fn fromteststruct2(a: TestFp2) -> Fp2 {
    (a.0.0, a.1.0)
}

fn fromteststruct6(a :TestFp6) -> Fp6 {
    (fromteststruct2(a.0), fromteststruct2(a.1), fromteststruct2(a.2))
}
fn fromteststruct12(a: TestFp12) -> Fp12 {
    (fromteststruct6(a.0), fromteststruct6(a.1))
}

//Sanity check helper functions
/*
fn to_hex(f: Fp) -> String {
    let s = Fp::to_byte_seq_be(f);
    Seq::to_hex(&s)
}

fn printfp12hex(f: Fp12) {
    println!("{}", to_hex(f.0.0.0));
    println!("{}", to_hex(f.0.0.1));
    println!("{}", to_hex(f.0.1.0));
    println!("{}", to_hex(f.0.1.1));
    println!("{}", to_hex(f.0.2.0));
    println!("{}", to_hex(f.0.2.1));
    println!("{}", to_hex(f.1.0.0));
    println!("{}", to_hex(f.1.0.1));
    println!("{}", to_hex(f.1.1.0));
    println!("{}", to_hex(f.1.1.1));
    println!("{}", to_hex(f.1.2.0));
    println!("{}", to_hex(f.1.2.1));
    
}
*/

#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements. Done via struct wrapper
fn test_fp2_prop_add_neg(a: (TestFp, TestFp)) -> bool {
    let a = (a.0.0, a.1.0);
    let b = fp2neg(a);
    fp2fromfp(Fp::ZERO()) == fp2add(a, b)
}


//Generating random numbers, taking inverse and multiplying - checking that random element times inverse gives one
#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements. Done via struct wrapper
fn test_fp2_prop_mul_inv(a: TestFp2) -> bool {
    let a = fromteststruct2(a);
    let b = fp2inv(a);
    fp2fromfp(Fp::ONE()) == fp2mul(a, b)
}

#[quickcheck]
fn test_fp2_prop_exp(a: TestFp2) -> bool {
    let a = fromteststruct2(a);
    let m = Scalar::from_literal(3u128);
    let n = Scalar::from_literal(4u128);
    let k = Scalar::from_literal(12u128);
    fp2exp(fp2exp(a, m), n) == fp2exp(a, k)
}

//Fp6 tests
#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements. Done via struct wrapper
fn test_fp6_prop_mul_inv(a: TestFp6) -> bool {
    let a = fromteststruct6(a);
    let b = fp6inv(a);
    fp6fromfp2(fp2fromfp(Fp::ONE())) == fp6mul(a, b)
}

#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements. Done via struct wrapper
fn test_fp6_prop_add_neg(a: TestFp6) -> bool {
    let a = fromteststruct6(a);
    let b = fp6neg(a);
    fp6fromfp2(fp2fromfp(Fp::ZERO())) == fp6add(a, b)
}

//Fp12 tests
#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements. Done via struct wrapper
fn test_fp12_prop_add_neg(a: TestFp12) -> bool {
    let a = fromteststruct12(a);
    let b = fp12neg(a);
    fp12fromfp6(fp6fromfp2(fp2fromfp(Fp::ZERO()))) == fp12add(a, b)
}

#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements. Done via struct wrapper
fn test_fp12_prop_mul_inv(a: TestFp12) -> bool {
    let a = fromteststruct12(a);
    let b = fp12inv(a);
    fp12fromfp6(fp6fromfp2(fp2fromfp(Fp::ONE()))) == fp12mul(a, b)
}

#[quickcheck]
fn test_fp12_prop_exp(a: TestFp12) -> bool {
    let a = fromteststruct12(a);
    let m = Scalar::from_literal(3u128);
    let n = Scalar::from_literal(4u128);
    let k = Scalar::from_literal(12u128);
    fp12exp(fp12exp(a, m), n) == fp12exp(a, k)
}

//G1 tests
#[test]
fn test_g1_arithmetic()
{
    let g = g1();

    let g2 = g1double(g);
    let g4a = g1double(g2);
    let g3 = g1add(g2, g);
    let g4b = g1add(g3, g);
    assert_eq!(g4a, g4b);
}


#[test]
fn test_g1_mul_prop() {
    fn test_g1_mul(a: TestScalar) -> bool
    {
        let g = g1mult(a.0, g1());
        let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r
        let h = g1mult(r, g);
        h.2
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new().tests(5).quickcheck(test_g1_mul as fn(TestScalar) -> bool);
}

//G2 tests
#[test]
fn test_g2_arithmetic()
{
    let g = g2();

    let g2 = g2double(g);
    let g4a = g2double(g2);
    let g3 = g2add(g2, g);
    let g4b = g2add(g3, g);
    assert_eq!(g4a, g4b);
}

#[test]
fn test_g2_mul_prop() {
    fn test_g2_mul(a: TestScalar) -> bool
    {
        let g = g2mult(a.0, g2());
        let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r
        let h = g2mult(r, g);
        h.2
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new().tests(5).quickcheck(test_g2_mul as fn(TestScalar) -> bool);
}



//Generators taken from:
//https://tools.ietf.org/id/draft-yonezawa-pairing-friendly-curves-02.html#rfc.section.4.2.2

//THIS IS A CORRECT G1 GENERATOR :)
fn g1() -> G1 {
    (Fp::from_hex("17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"),
    Fp::from_hex("08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1"), false)
}

//THIS IS A CORRECT G2 GENERATOR :)
fn g2() -> G2 {
    ((Fp::from_hex("24aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8"),
    Fp::from_hex("13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e")), 
    (Fp::from_hex("0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801"), 
    Fp::from_hex("0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be")), false)
}


//Testing the cofactor multiplication and integer times group element
#[test]
fn test_g1_generator() {
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r

    let aa = g1();
    let dd = g1mult(r, aa);
    assert!(dd.2);
}

#[test]
fn test_g2_generator() {
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r

    let a = g2();
    let b = g2mult(r, a);
    assert!(b.2);

}

#[quickcheck] //To Do: Property Quick-test
fn test_frob(a: TestFp12) -> bool {
    let a = fromteststruct12(a);
    let b = frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(a))))))))))));
    let c = frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(a))))));
    a == b && a == fp12conjugate(c)
}

#[test]
fn test_pairing_bilinearity() {
    let a = Scalar::from_literal(9483274923u128);
    let b = Scalar::from_literal(124959043234u128);
    let c = a * b;
    
    let p = pairing(g1mult(a, g1()), g2mult(b, g2()));
    //e(a*g1, b*g2) = e(c*g1, g2) = e(g1, g1)*c with c = a * b
    assert_eq!(p, pairing(g1mult(c, g1()), g2()));
    //e(a*g1, b*g2) = e(g1, g2)^(a*b)
    assert_eq!(p, fp12exp(pairing(g1(), g2()), c)); 
}   

#[test]
fn test_pairing_unitary() {
    let p = fp12conjugate(pairing(g1(), g2()));
    let q = pairing(g1(), g2neg(g2()));
    let r = pairing(g1neg(g1()), g2());
    assert_eq!(p, q);
    assert_eq!(q, r);
}



//Just a valid Fp12 point... Nothing special
fn fp12point() -> Fp12 {
    (((Fp::from_hex("12afbc6d6c71900c6228f0ec4a5ae91aa7747a0ddf39cde0062f71e950e716a8ae27ad686e700608f35e3f6c0fe0cf11"),
    Fp::from_hex("1660f8efaccc7a77268d7e17a31926b2d58879922f0d430c39c891867c64bc5baa8ed0f8350626ffb592eefa8248e536")), 
    (Fp::from_hex("13792df9b2c7e814fc6308f1ae6d641d7ae658d99725318b86104868ea3cbf8b94b0c2d4393c86a9d36641d22d0464e8"),
    Fp::from_hex("16544b2b2595abd69b014bb2974cbc110787f2c4752b82c5460aaf9030eea1bce7ca11ebea791ba3622feb024b198431")),
    (Fp::from_hex("12236e4849c69ecded8037549af297183f7be830f54e417e7970dd014027bc7aafc6485397113e65cc3079d1cf6fb1ba"),
    Fp::from_hex("0934eeb51f85c8f0f34cb411a049ed9fe6215f775bebea5d757fb589dbd1821b2eb7c026f779ea0705b984764bbc3e22"))),
    ((Fp::from_hex("149f6bdeb04b4be589c319b54a03b43960dd59a9f1a27c575caa5bc95614db83fc2ac87b521c7a37573e85ae9cc11284"),
    Fp::from_hex("10bea874008cbcdf99d6f7e3dd03ee47106f2cf83597795795a30c2cc5a818af7ae2e6d0b00f0a0cd563c3d592332a7a")),
    (Fp::from_hex("0edda465a41e2be599242c5e78280ced388f4d7fb5d77c8b87bcc2665f024ede6c29cbaff8b710391d0fcde8d02618e1"),
    Fp::from_hex("0e8edc9ff2b93b5af140ff42e1b2998fd15dcb07d1af0e3b6a844c8b521c7885886ede9bff112cb5a35b4d9898ef65f9")),
    (Fp::from_hex("0b362f9cb09944d3f759991bfc72aafd9930f719cf5390164b32d859b4090cc251b8117255a8358ed19ba3026e45c5c0"),
    Fp::from_hex("005ffbaef16f69b249e9f9c81a913a9f1cc1c96154cfb89d00f769efcad52ef81aba95e1e3de33912e7a0f97b83972e5"))))
}


//  (f^((p^12-1)/r))^r = f^(p^12-1) = f^p^12*f^-1 = f*f^-1 = 1
#[test]
fn test_final_exponentiation_rth_root() {
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r
    let one = fp12fromfp6(fp6fromfp2(fp2fromfp(Fp::ONE())));
    let f = fp12point();
    let ffinal = final_exponentiation(f);
    let fr = fp12exp(ffinal, r);
    assert_eq!(fr, one);
}

