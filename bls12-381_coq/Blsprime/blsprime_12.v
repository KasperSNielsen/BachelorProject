From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma blsprime12:
  prime  28421776371202422728422932661->
  prime  496889763006522815900371787705259082273541.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      496889763006522815900371787705259082273541
      17482713132244
      ((28421776371202422728422932661,1)::nil)
      900
      0
      90
      900)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
