From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma blsprime16:
  prime  9071203->
  prime  8064160813.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      8064160813
      889
      ((9071203,1)::nil)
      0
      123462
      19
      361)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
