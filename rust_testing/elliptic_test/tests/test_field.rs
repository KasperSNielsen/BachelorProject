use elliptic_test::*;
use hacspec_lib::*;


#[test]
fn test_point() {
    let (x1, x2) = fieldfis();
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
    let p1 = (FieldElement::from_literal(5), FieldElement::from_literal(22));
    let p2 = (FieldElement::from_literal(16), FieldElement::from_literal(27));
    let result = add(p1, p2);
    assert_eq!(result, (FieldElement::from_literal(13), FieldElement::from_literal(6)));


}
