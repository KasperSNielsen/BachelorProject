use hacspec_lib::*;

const IVSIZE: usize = 12;
bytes!(Nonce, IVSIZE);

bytes!(Tau, 8);

public_nat_mod!(
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "8000000000000000000000000000000000000000000000000000000000000000"
);


pub fn three(nonce: Nonce) -> BigInt {
    
    let test = Tau::new();
    let mut nonce2 = nonce;
    nonce2[1] = U8::classify(67);

    let x = BigInt::from_literal(12u128);   
    let one = BigInt::ONE();
    let x = x.wrap_add(one); //x = x+1, ie 13. Note: comsumes x so need to assign to new one
    // 

    //let one: BigInt = BigInt::ZERO();


    x

}

