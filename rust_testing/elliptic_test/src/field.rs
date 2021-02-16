use hacspec_lib::*;


public_nat_mod!( //Custom Macro - defining a newtype with some functions - well defined macro's have library functions built in
    type_name: FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 5,
    modulo_value: "1d"
);
// p192 = 2^192 - 2^64 - 1
//16^48 - 16^16 - 1

type Point = (FieldElement, FieldElement);

pub fn fieldfis() -> Point {
    let zero = FieldElement::ZERO(); //Create element Zero from public_nat_mod macro called FieldElement
    let two = FieldElement::TWO(); // Same as above
    let maxval = FieldElement::max_val(); //Create max value, add 2, which would equal 1 under the mod
    (zero, two + maxval)
}


pub fn add(p: Point, q: Point) -> Point
{
    let (x_1, y_1) = p;
    let (x_2, y_2) = q;

    let x_diff = x_2 - x_1; 
    let y_diff = y_2 - y_1;

    let xovery = y_diff * x_diff.inv(); //  x / y = x * y^-1
    let x_3 = xovery.exp(2) - x_1 - x_2;
    let y_3 = xovery * (x_1 - x_3) - y_1;

    (x_3, y_3)
}
