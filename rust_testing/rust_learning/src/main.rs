use std::io;
//use rand::Rng;
//use std::cmp::Ordering;

fn main() {
    //let foo = "test";
    let mut test = String::from("Hello, ");
    test.push_str("world");
    
    // 2\n3\n


    //let rand = rand::thread_rng().gen_range(1,11);
    let mut guess = String::new();

    for _ in 0..2
    {
        println!("Enter input");
        

        io::stdin().read_line(&mut guess).expect("Failed to read line"); //Appends to current given string!
        println!("String: {}", guess);
    }
    
    //println!("Secret = {}", rand);


}
