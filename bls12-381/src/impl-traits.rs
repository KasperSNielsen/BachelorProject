use hacspec_bls12_381::*;
use group::{prime::{PrimeCurve, PrimeCurveAffine},
    Group, UncompressedEncoding};
use pairing::PairingCurveAffine;

#[derive(Debug)]
struct G1wrap(G1);

#[derive(Debug)]
struct G2wrap(G2);

#[derive(Debug)]
struct Fp12wrap(Fp12);


impl PairingCurveAffine for G1wrap {
    type Pair = G2wrap;
    type PairingResult = Fp12wrap;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult
    {
        Fp12wrap(pairing(self.0, other.0))
    }
}

impl PairingCurveAffine for G2wrap {
    type Pair = G1wrap;
    type PairingResult = Fp12wrap;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult
    {
        Fp12wrap(pairing(other.0, self.0))
    }
}

// ############################################# TESTS ############################################# 



fn g1() -> G1 {
    (Fp::from_hex("17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"),
    Fp::from_hex("08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1"), false)
}

//THIS IS A CORRECT G2 GENERATOR :)
fn g2() -> G2 {
    ((Fp::from_hex("24aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8"),
    Fp::from_hex("13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e")), 
    (Fp::from_hex("0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801"), 
    Fp::from_hex("0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be")), false)
}


#[test]
fn test_traits() {
    let g1: G1 = g1();
    let g2: G2 = g2();
    g1.pairing_with(g1, g2);