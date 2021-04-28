From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma blsprime14:
  prime  1797920715053357->
  prime  227332381811363445780697.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      227332381811363445780697
      126441828
      ((1797920715053357,1)::nil)
      18
      0
      3
      9)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
