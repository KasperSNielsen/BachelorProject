## BLS12-381 Hacspec implementation and Coq equivalence proof
This is the bachelor project of Kasper S. Nielsen and Mathias Rud Laursen from Aarhus University.
The project consists of implementing the BLS12-381 curve in hacspec and proving the correctness of it.

### Usage
To use the project, the following dependencies are required
 - hacspec: Download from https://github.com/hacspec/hacspec
 - Rust: Install from official website
 - Opam: ```apt install opam; opam init ```
 - Coq: ``` opam install coq ```. Also install required dependencies 

Add repositories to install CompCert and Fiat-Crypto:
 - ```opam repo add coq-released https://coq.inria.fr/opam/released ```
 - ```opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev ```

Install CompCert, Coqprime and Fiat-Crypto:
 - CompCert version 3.8: ```opam pin add coq-compcert 3.8 ```
 - Coqprime cersion 1.0.6: ```opam pin add coq-coqprime 1.0.6 ```
 - Fiat-Crypto: ```opam install coq-fiat-crypto```
 
 
### Folder Structure
 - blS12-381: Contains the implementation of the BLS12-381 curve used in the project. Also contains the specific tests used.
 - rust_testing: A playground used for testing rust - this can be disregarded.
 - coq_learning: A playground used for learning Coq - this can be disregarded.
 - bls12-381_coq: Contains the relevant Coq files used in the project to prove correctness of the implementation

### About the project ###
The project consisted of two parts: Specifying an implementation of the BLS12-381 curve in hacspec, and proving the correctness of it. The correctness proof consists of showing an equivalence of the group laws for G1 and G2, between the hacspec specification, and the fiat-crypto specification.

To compile the Coq files, use the make file provided in _bls12-381_coq_.
The proof of equivalence can be found in _bls.v_, while a proof showing that our prime _p_ indeed is a prime can be found in _blsprime.v_
