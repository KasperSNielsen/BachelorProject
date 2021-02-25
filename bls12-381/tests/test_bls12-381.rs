use bls12_381::*;
use hacspec_lib::*;

//Helper function: Takes LE u64 array input and retuns an FP element. So we can 'steal' tests from https://github.com/zkcrypto/bls12_381
fn fpfromarray(a: [u64; 6]) -> Fp {
    let mut b: [u8; 48] = [0; 48];
    for i in 0..6 {
        let val: u64 = a[i];
        b[(i*8)..((i+1)*8)].copy_from_slice(&(val.to_le_bytes()));
    }
    Fp::from_byte_seq_le(SerializedFp::from_public_slice(&b))
}

#[test]
fn test_add_sub() {
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