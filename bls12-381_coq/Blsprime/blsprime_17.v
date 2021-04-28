From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma blsprime17 : prime 9071203.
Proof.
 apply (Pocklington_refl
         (Pock_certif 9071203 2 ((215981, 1)::(2,1)::nil) 1)
        ((Pock_certif 215981 2 ((10799, 1)::(2,2)::nil) 1) ::
         (Proof_certif 10799 prime10799) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

