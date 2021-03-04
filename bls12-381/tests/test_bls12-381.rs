/* TO DO: Property Tests with associativity and distributive law */


use bls12_381::*;
use hacspec_lib::*;

#[cfg(test)]
extern crate quickcheck;
use quickcheck::*;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

//Helper function: Takes LE u64 array input and retuns an FP element. So we can 'steal' tests from https://github.com/zkcrypto/bls12_381
fn fpfromarray(a: [u64; 6]) -> Fp {
    let mut b: [u8; 48] = [0; 48];
    for i in 0..6 {
        let val: u64 = a[i];
        b[(i*8)..((i+1)*8)].copy_from_slice(&(val.to_le_bytes()));
    }
    Fp::from_byte_seq_le(SerializedFp::from_public_slice(&b))
}
/* Property Based Testing features, needed to perform testing */

//Wrapper around Fp, so we can implement arbitrary
#[derive(Debug)]
#[derive(Clone)]
struct TestFp(Fp);
type TestFp2 = (TestFp, TestFp);
type TestFp6 = (TestFp2, TestFp2, TestFp2);
type TestFp12 = (TestFp6, TestFp6);

/* Arbitrary Implementation used for Property Based Tests */
#[cfg(test)]
impl Arbitrary for TestFp {
    fn arbitrary(g: &mut Gen) -> TestFp {
        let mut a: [u64; 6] = [0; 6];
        for i in 0..6 {
            a[i] = u64::arbitrary(g);
        }
        TestFp(fpfromarray(a))
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


#[test]
fn test_add_neg() {
    let b = (fpfromarray([
        0xa1e0_9175_a4d2_c1fe,
        0x8b33_acfc_204e_ff12,
        0xe244_15a1_1b45_6e42,
        0x61d9_96b1_b6ee_1936,
        0x1164_dbe8_667c_853c,
        0x0788_557a_cc7d_9c79,
    ]),
    fpfromarray([
        0xda6a_87cc_6f48_fa36,
        0x0fc7_b488_277c_1903,
        0x9445_ac4a_dc44_8187,
        0x0261_6d5b_c909_9209,
        0xdbed_4677_2db5_8d48,
        0x11b9_4d50_76c7_b7b1,
    ]));
    let a = fp2neg(b);
    assert_eq!(fp2add(a, b), fp2fromfp(Fp::ZERO()));
}

#[quickcheck] //Using the fp arbitraty implementation from above to generate fp2 elements. Done via struct wrapper
fn test_fp2_prop_add_neg(a: (TestFp, TestFp)) -> bool {
    let a = (a.0.0, a.1.0);
    let b = fp2neg(a);
    fp2fromfp(Fp::ZERO()) == fp2add(a, b)
}


#[test]
fn test_mul_inv() {
    let b = (fpfromarray([
        0xa1e0_9175_a4d2_c1fe,
        0x8b33_acfc_204e_ff12,
        0xe244_15a1_1b45_6e42,
        0x61d9_96b1_b6ee_1936,
        0x1164_dbe8_667c_853c,
        0x0788_557a_cc7d_9c79,
    ]),
    fpfromarray([
        0xda6a_87cc_6f48_fa36,
        0x0fc7_b488_277c_1903,
        0x9445_ac4a_dc44_8187,
        0x0261_6d5b_c909_9209,
        0xdbed_4677_2db5_8d48,
        0x11b9_4d50_76c7_b7b1,
    ]));
    let a = fp2inv(b);
    assert_eq!(fp2mul(a, b), fp2fromfp(Fp::ONE()));
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
    let g = (fpfromarray([
        0x5cb3_8790_fd53_0c16,
        0x7817_fc67_9976_fff5,
        0x154f_95c7_143b_a1c1,
        0xf0ae_6acd_f3d0_e747,
        0xedce_6ecc_21db_f440,
        0x1201_7741_9e0b_fb75,
    ]),
    fpfromarray([
        0xbaac_93d5_0ce7_2271,
        0x8c22_631a_7918_fd8e,
        0xdd59_5f13_5707_25ce,
        0x51ac_5829_5040_5194,
        0x0e1c_8c3f_ad00_59c0,
        0x0bbc_3efc_5008_a26a,
    ]));

    let g2 = g1double(g);
    let g4a = g1double(g2);
    let g3 = g1add(g2, g);
    let g4b = g1add(g3, g);
    assert_eq!(g4a, g4b);
}

#[test]
fn test_g1_mul()
{
    let g = (fpfromarray([
        0x5cb3_8790_fd53_0c16,
        0x7817_fc67_9976_fff5,
        0x154f_95c7_143b_a1c1,
        0xf0ae_6acd_f3d0_e747,
        0xedce_6ecc_21db_f440,
        0x1201_7741_9e0b_fb75,
    ]),
    fpfromarray([
        0xbaac_93d5_0ce7_2271,
        0x8c22_631a_7918_fd8e,
        0xdd59_5f13_5707_25ce,
        0x51ac_5829_5040_5194,
        0x0e1c_8c3f_ad00_59c0,
        0x0bbc_3efc_5008_a26a,
    ]));

    let s = Scalar::from_literal(11);
    let g11a = g1mult(s, g);
    let g2 = g1double(g);
    let g4 = g1double(g2);
    let g8 = g1double(g4);
    let g10 = g1add(g8, g2);
    let g11b = g1add(g10, g);
    assert_eq!(g11a, g11b);
}

//G2 tests
#[test]
fn test_g2_arithmetic()
{
    let g = ((fpfromarray([
            0xf5f2_8fa2_0294_0a10,
            0xb3f5_fb26_87b4_961a,
            0xa1a8_93b5_3e2a_e580,
            0x9894_999d_1a3c_aee9,
            0x6f67_b763_1863_366b,
            0x0581_9192_4350_bcd7,
        ]),
        fpfromarray([
            0xa5a9_c075_9e23_f606,
            0xaaa0_c59d_bccd_60c3,
            0x3bb1_7e18_e286_7806,
            0x1b1a_b6cc_8541_b367,
            0xc2b6_ed0e_f215_8547,
            0x1192_2a09_7360_edf3,
        ])),
        (fpfromarray([
            0x4c73_0af8_6049_4c4a,
            0x597c_fa1f_5e36_9c5a,
            0xe7e6_856c_aa0a_635a,
            0xbbef_b5e9_6e0d_495f,
            0x07d3_a975_f0ef_25a2,
            0x0083_fd8e_7e80_dae5,
        ]),
        fpfromarray([
            0xadc0_fc92_df64_b05d,
            0x18aa_270a_2b14_61dc,
            0x86ad_ac6a_3be4_eba0,
            0x7949_5c4e_c93d_a33a,
            0xe717_5850_a43c_caed,
            0x0b2b_c2a1_63de_1bf2,
        ])));

    let g2 = g2double(g);
    let g4a = g2double(g2);
    let g3 = g2add(g2, g);
    let g4b = g2add(g3, g);
    assert_eq!(g4a, g4b);
}

#[test]
fn test_g2_mul()
{
    let g = ((fpfromarray([
        0xf5f2_8fa2_0294_0a10,
        0xb3f5_fb26_87b4_961a,
        0xa1a8_93b5_3e2a_e580,
        0x9894_999d_1a3c_aee9,
        0x6f67_b763_1863_366b,
        0x0581_9192_4350_bcd7,
    ]),
    fpfromarray([
        0xa5a9_c075_9e23_f606,
        0xaaa0_c59d_bccd_60c3,
        0x3bb1_7e18_e286_7806,
        0x1b1a_b6cc_8541_b367,
        0xc2b6_ed0e_f215_8547,
        0x1192_2a09_7360_edf3,
    ])),
    (fpfromarray([
        0x4c73_0af8_6049_4c4a,
        0x597c_fa1f_5e36_9c5a,
        0xe7e6_856c_aa0a_635a,
        0xbbef_b5e9_6e0d_495f,
        0x07d3_a975_f0ef_25a2,
        0x0083_fd8e_7e80_dae5,
    ]),
    fpfromarray([
        0xadc0_fc92_df64_b05d,
        0x18aa_270a_2b14_61dc,
        0x86ad_ac6a_3be4_eba0,
        0x7949_5c4e_c93d_a33a,
        0xe717_5850_a43c_caed,
        0x0b2b_c2a1_63de_1bf2,
    ])));

    let s = Scalar::from_literal(11);
    let g11a = g2mult(s, g);
    let g2 = g2double(g);
    let g4 = g2double(g2);
    let g8 = g2double(g4);
    let g10 = g2add(g8, g2);
    let g11b = g2add(g10, g);
    assert_eq!(g11a, g11b);
}

//Testing the rather complex helper function for sanity check
#[test]
fn test_helper() {
    let a = fpfromarray([
        0xc9a2_1831_63ee_70d4,
        0xbc37_70a7_196b_5c91,
        0xa247_f8c1_304c_5f44,
        0xb01f_c2a3_726c_80b5,
        0xe1d2_93e5_bbd9_19c9,
        0x04b7_8e80_020e_f2ca,
    ]);
    let b = Fp::from_byte_seq_be(SerializedFp::from_hex("04b78e80020ef2cae1d293e5bbd919c9b01fc2a3726c80b5a247f8c1304c5f44bc3770a7196b5c91c9a2183163ee70d4"));
    assert_eq!(a, b);
}

fn g1() -> G1 {
    (fpfromarray([
    0x5cb3_8790_fd53_0c16,
    0x7817_fc67_9976_fff5,
    0x154f_95c7_143b_a1c1,
    0xf0ae_6acd_f3d0_e747,
    0xedce_6ecc_21db_f440,
    0x1201_7741_9e0b_fb75,
    ]),
    fpfromarray([
        0xbaac_93d5_0ce7_2271,
        0x8c22_631a_7918_fd8e,
        0xdd59_5f13_5707_25ce,
        0x51ac_5829_5040_5194,
        0x0e1c_8c3f_ad00_59c0,
        0x0bbc_3efc_5008_a26a,
    ]))
}

fn g2() -> G2 {
    ((fpfromarray([
        0xf5f2_8fa2_0294_0a10,
        0xb3f5_fb26_87b4_961a,
        0xa1a8_93b5_3e2a_e580,
        0x9894_999d_1a3c_aee9,
        0x6f67_b763_1863_366b,
        0x0581_9192_4350_bcd7,
    ]),
    fpfromarray([
        0xa5a9_c075_9e23_f606,
        0xaaa0_c59d_bccd_60c3,
        0x3bb1_7e18_e286_7806,
        0x1b1a_b6cc_8541_b367,
        0xc2b6_ed0e_f215_8547,
        0x1192_2a09_7360_edf3,
    ])),

(fpfromarray([
        0x4c73_0af8_6049_4c4a,
        0x597c_fa1f_5e36_9c5a,
        0xe7e6_856c_aa0a_635a,
        0xbbef_b5e9_6e0d_495f,
        0x07d3_a975_f0ef_25a2,
        0x0083_fd8e_7e80_dae5,
    ]),
    fpfromarray([
        0xadc0_fc92_df64_b05d,
        0x18aa_270a_2b14_61dc,
        0x86ad_ac6a_3be4_eba0,
        0x7949_5c4e_c93d_a33a,
        0xe717_5850_a43c_caed,
        0x0b2b_c2a1_63de_1bf2,
    ])))
}

fn gt() -> Fp12 {
    (((fpfromarray([
        0x1972_e433_a01f_85c5,
        0x97d3_2b76_fd77_2538,
        0xc8ce_546f_c96b_cdf9,
        0xcef6_3e73_66d4_0614,
        0xa611_3427_8184_3780,
        0x13f3_448a_3fc6_d825,
        ]),
        fpfromarray([
            0xd263_31b0_2e9d_6995,
            0x9d68_a482_f779_7e7d,
            0x9c9b_2924_8d39_ea92,
            0xf480_1ca2_e131_07aa,
            0xa16c_0732_bdbc_b066,
            0x083c_a4af_ba36_0478,
        ])),
    
    (fpfromarray([
            0x59e2_61db_0916_b641,
            0x2716_b6f4_b23e_960d,
            0xc8e5_5b10_a0bd_9c45,
            0x0bdb_0bd9_9c4d_eda8,
            0x8cf8_9ebf_57fd_aac5,
            0x12d6_b792_9e77_7a5e,
        ]),
        fpfromarray([
            0x5fc8_5188_b0e1_5f35,
            0x34a0_6e3a_8f09_6365,
            0xdb31_26a6_e02a_d62c,
            0xfc6f_5aa9_7d9a_990b,
            0xa12f_55f5_eb89_c210,
            0x1723_703a_926f_8889,
        ])),
    (fpfromarray([
            0x9358_8f29_7182_8778,
            0x43f6_5b86_11ab_7585,
            0x3183_aaf5_ec27_9fdf,
            0xfa73_d7e1_8ac9_9df6,
            0x64e1_76a6_a64c_99b0,
            0x179f_a78c_5838_8f1f,
        ]),
        fpfromarray([
            0x672a_0a11_ca2a_ef12,
            0x0d11_b9b5_2aa3_f16b,
            0xa444_12d0_699d_056e,
            0xc01d_0177_221a_5ba5,
            0x66e0_cede_6c73_5529,
            0x05f5_a71e_9fdd_c339,
        ]))),
((fpfromarray([
            0xd30a_88a1_b062_c679,
            0x5ac5_6a5d_35fc_8304,
            0xd0c8_34a6_a81f_290d,
            0xcd54_30c2_da37_07c7,
            0xf0c2_7ff7_8050_0af0,
            0x0924_5da6_e2d7_2eae,
        ]),
        fpfromarray([
            0x9f2e_0676_791b_5156,
            0xe2d1_c823_4918_fe13,
            0x4c9e_459f_3c56_1bf4,
            0xa3e8_5e53_b9d3_e3c1,
            0x820a_121e_21a7_0020,
            0x15af_6183_41c5_9acc,
        ])),
    (fpfromarray([
            0x7c95_658c_2499_3ab1,
            0x73eb_3872_1ca8_86b9,
            0x5256_d749_4774_34bc,
            0x8ba4_1902_ea50_4a8b,
            0x04a3_d3f8_0c86_ce6d,
            0x18a6_4a87_fb68_6eaa,
        ]),
        fpfromarray([
            0xbb83_e71b_b920_cf26,
            0x2a52_77ac_92a7_3945,
            0xfc0e_e59f_94f0_46a0,
            0x7158_cdf3_7860_58f7,
            0x7cc1_061b_82f9_45f6,
            0x03f8_47aa_9fdb_e567,
        ])),
    (fpfromarray([
            0x8078_dba5_6134_e657,
            0x1cd7_ec9a_4399_8a6e,
            0xb1aa_599a_1a99_3766,
            0xc9a0_f62f_0842_ee44,
            0x8e15_9be3_b605_dffa,
            0x0c86_ba0d_4af1_3fc2,
        ]),
        fpfromarray([
            0xe80f_f2a0_6a52_ffb1,
            0x7694_ca48_721a_906c,
            0x7583_183e_03b0_8514,
            0xf567_afdd_40ce_e4e2,
            0x9a6d_96d2_e526_a5fc,
            0x197e_9f49_861f_2242,
        ]))))
}

#[test]
fn test_test() {
    let c1 = ArrayFp(secret_array!(
        U64,
        [0x0708_9552_b319_d465u64,
        0xc669_5f92_b50a_8313u64,
        0x97e8_3ccc_d117_228fu64,
        0xa35b_aeca_b2dc_29eeu64,
        0x1ce3_93ea_5daa_ce4du64,
        0x08f2_220f_b0fb_66ebu64]
    ));
    let c1 = ArrayFp::to_le_bytes(&c1);
    let c1 = Fp::from_byte_seq_le(c1);

    let c2 = fpfromarray(
        [0x0708_9552_b319_d465,
        0xc669_5f92_b50a_8313,
        0x97e8_3ccc_d117_228f,
        0xa35b_aeca_b2dc_29ee,
        0x1ce3_93ea_5daa_ce4d,
        0x08f2_220f_b0fb_66eb]);
    assert_eq!(c1, c2);
}

#[test]
fn test_test2() {
    let p = Scalar::from_hex("1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab");
    let k = (p - Scalar::ONE()) / Scalar::from_literal(6u128);
    let xi = (Fp::ONE(), Fp::ONE());
    let s = fp2exp(xi, k);

    let c1 = ArrayFp(secret_array!(
        U64,
        [0x0708_9552_b319_d465u64,
        0xc669_5f92_b50a_8313u64,
        0x97e8_3ccc_d117_228fu64,
        0xa35b_aeca_b2dc_29eeu64,
        0x1ce3_93ea_5daa_ce4du64,
        0x08f2_220f_b0fb_66ebu64]
    ));

    let c1 = ArrayFp::to_le_bytes(&c1);
    let c1 = Fp::from_byte_seq_le(c1);

    let c2 = ArrayFp(secret_array!(
        U64,
        [0xb2f6_6aad_4ce5_d646u64,
        0x5842_a06b_fc49_7cecu64,
        0xcf48_95d4_2599_d394u64,
        0xc11b_9cba_40a8_e8d0u64,
        0x2e38_13cb_e5a0_de89u64,
        0x110e_efda_8884_7fafu64]
    ));

    let c2 = ArrayFp::to_le_bytes(&c2);
    let c2 = Fp::from_byte_seq_le(c2);
    
    let gamma11 = (c1, c2);

    assert_eq!(s, gamma11);
}

#[test]
fn test_frob() {
    let a = gt();
    let b = frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(frobenius(a))))))))))));
    assert_eq!(a, b)
}

#[test]
fn test_pairing() {
    

    //assert_eq!(pairing(g1(), g2()), gt())
    assert_eq!(pairing(g1mult(Scalar::TWO(), g1()), g2()), fp12exp(pairing(g1(), g2()), Scalar::TWO()));
}