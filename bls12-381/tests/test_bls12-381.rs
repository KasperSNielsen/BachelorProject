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
fn test_prop_add_neg(a: (TestFp, TestFp)) -> bool {
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
fn test_prop_mul_inv(a: (TestFp, TestFp)) -> bool {
    let a = (a.0.0, a.1.0);
    let b = fp2inv(a);
    fp2fromfp(Fp::ONE()) == fp2mul(a, b)
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

