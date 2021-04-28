From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma blsprime13:
  prime  227332381811363445780697->
  prime  28421776371202422728422932661.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      28421776371202422728422932661
      125023
      ((227332381811363445780697,1)::nil)
      0
      47250
      15
      225)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
