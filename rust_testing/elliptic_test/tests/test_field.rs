use elliptic_test::*;
use hacspec_lib::*;


#[test]
fn test_point() {
    let (x1, x2, inf) = fieldfis();
    let y1 = FieldElement::from_literal(0u128);
    let y2 = FieldElement::from_literal(1u128);
    assert_eq!(x1, y1);
    assert_eq!(x2, y2); //Asserts that the modulo actually wraps around correctly
}

#[test]
fn test_inv()
{
    let x = FieldElement::from_literal(3u128);
    let x_inv = x.inv();
    println!("{}", x_inv); //Prints 10; Inverse: a^-1: a, so ax = 1 mod p
                           // 10*30 = 30 = 1 mod 29 so it works
    println!("{}", FieldElement::from_literal(10) * x_inv); 
}

#[test]
fn test_add()
{
    let p1 = (FieldElement::from_literal(5), FieldElement::from_literal(22), false);
    let p2 = (FieldElement::from_literal(16), FieldElement::from_literal(27), false);
    let result = add(p1, p2);
    assert_eq!(result, (FieldElement::from_literal(13), FieldElement::from_literal(6), false));


}

#[test]
fn test_double()
{
    let p = (FieldElement::from_literal(5), FieldElement::from_literal(22), false);
    let result = double(p, FieldElement::from_literal(4));
    assert_eq!(result, (FieldElement::from_literal(14), FieldElement::from_literal(6), false));
}

#[test]
fn test_add_double() // [2]([2]p) = 2p + p + p
{
    let p = (FieldElement::from_literal(27), FieldElement::from_literal(2), false);
    let p2 = double(p, FieldElement::from_literal(4));
    let p4_1 = double(p2, FieldElement::from_literal(4));
    let p3 = add(p2, p);
    let p4_2 = add(p3, p);
    assert_eq!(p4_1, p4_2);
}

#[test]
fn test_bit_order() 
{
    let n = Scalar::from_literal(7);
    println!("{}", most_significant_bit(n, 6)); //Checks from least to most significant bit 00000111
    for i in 6..0 {
        println!("{}", i);
    }
}

#[test]
fn test_mult() {
    let p = (FieldElement::from_literal(27), FieldElement::from_literal(2), false);
    let p2 = double(p, FieldElement::from_literal(4));
    let p3 = add(p2, p);
    let p6_1 = double(p3, FieldElement::from_literal(4));
    let p6_2 = mult(Scalar::from_literal(6), p, FieldElement::from_literal(4));
    assert_eq!(p6_1, p6_2);
}