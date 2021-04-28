From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma blsprime15:
  prime  8064160813->
  prime  1797920715053357.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1797920715053357
      222952
      ((8064160813,1)::nil)
      1797920715053321
      0
      12
      36)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
