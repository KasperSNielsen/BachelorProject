From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma blsprime10:
  prime  1342795879390558010604340264273237636919190426965557->
  prime  286888339631792718965617297487910701532064205611864181861.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      286888339631792718965617297487910701532064205611864181861
      213650
      ((1342795879390558010604340264273237636919190426965557,1)::nil)
      107583127361922269612106486557966513074524077104449068199
      0
      143444169815896359482808648743955350766032102805932090932
      215166254723844539224212973115933026149048154208898136398)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.