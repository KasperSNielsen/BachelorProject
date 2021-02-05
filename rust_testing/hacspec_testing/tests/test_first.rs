use hacspec_testing::*;
use hacspec_lib::*;

#[test]
fn test_three() 
{

    let x = U32::classify(1u32);

    let nonce2 = Nonce::from_public_slice(&[
        0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb,
    ]); //Create array of type Nonce
    let x: BigInt = three(nonce2);
    
    /*let y: U8 = nonce[1];
    assert_eq!(y.declassify(), 67);
    assert_eq!(declassify_u8_from_U8(nonce[1]), 67);
    for i in 0..12 {
        println!("{}", nonce[i]) //Printing the stuff from first.rs
    }
    */
    println!("{}", x) //Printing the stuff from first.rs
}