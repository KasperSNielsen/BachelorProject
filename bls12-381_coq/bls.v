(*In this file, we provide a proof, that the bls12-381 specification, written in hacspec is equivalent to the Weierstrass curve specification, from the fiat-crypto project. 
This work has been done using a compiler from hacspec to Coq, and then proofs and lemmas have been constructed to finalise the proof. 
The bls12-381 specification can be found here: https://github.com/hacspec/hacspec/blob/master/examples/bls12-381/src/bls12-381.rs
The fiat-crypto Weierstrass curve specification can be found here: https://github.com/mit-plv/fiat-crypto/blob/master/src/Spec/WeierstrassCurve.v

The file contains all needed steps, for specifying a translation between the hacspec specification and the fiat-crypto one, as well as a the final proof, showing equivalence *)


Require Import Lib.
Require Import IntTypes.
From Coq Require Import ZArith.
Require Import List. Import ListNotations.
Open Scope hacspec_scope.
Open Scope bool_scope.
From Coqprime Require Import GZnZ.

Notation "a >?? b" := (Nat.ltb b a) (at level 79).

(* uint_size = nat *)


Definition prime := 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab%Z.

Definition fp : Type := znz prime.


Definition g1 : Type := (fp * fp * bool).
Definition fp2 : Type := (fp * fp).
Definition g2 : Type := (fp2 * fp2 * bool).
Definition fp6 : Type := (fp2 * fp2 * fp2).
Definition fp12 : Type := (fp6 * fp6).

Definition fp_canvas := lseq (pub_uint8) (48).


Definition serialized_fp := lseq (uint8) (usize 48).

Definition array_fp := lseq (uint64) (usize 6).

Definition scalar_canvas := lseq (pub_uint8) (32).

Module Wordsize_256.
  Definition wordsize : nat := 256.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
  (* Proof. unfold wordsize; congruence. Qed. *)
End Wordsize_256.
Strategy opaque [Wordsize_256.wordsize].

Module nat_mod_256 := Integers.Make(Wordsize_256).
(* Import nat_mod_256. *)

Definition scalar :=
  nat_mod_256.int.

(* TODO *)
Axiom nat_bit : N -> scalar -> uint_size -> bool.
Axiom most_significant_bit : scalar -> uint_size -> uint_size.
Axiom N_to_int : N -> fp. 
Coercion N_to_int : N >-> fp.
Coercion Z.of_N : N >-> Z.

(* TODO: write a coq-friendly version of this (coq can't find decreasing fix of the body) *)
(* Fixpoint most_significant_bit (m_0 : scalar) (n_1 : uint_size) : uint_size :=
  if (
    ((n_1) >?? (usize 0)) && (
      negb (
        nat_bit (
          256) (
          m_0) (n_1)))) then (
    most_significant_bit (m_0) ((n_1) - (usize 1))) else (n_1). *)

Check add.

Definition fp_add := add prime.
Definition fp_sub := sub prime.
Definition fp_mul := mul prime.
Definition fp_neg := opp prime.

Infix "-" := fp_sub.
Infix "+" := fp_add.
Infix "*" := fp_mul.

Definition fp_zero := zero prime.
Definition fp_one := one prime.
Definition fp_two := fp_one + fp_one.
Definition fp_three := fp_one + fp_two.
Definition fp_four := fp_one + fp_three.

Definition fp_exp (x y : fp) := x * x.

Definition fp_inv := inv prime.

Definition fp_div := div prime.

Definition fp_val := val prime.

Definition fp_eqb x y := Z.eqb (fp_val x) (fp_val y).


Definition fp2fromfp (n_2 : fp) : fp2 :=
(
  n_2,
  fp_zero
).

Definition fp2zero : fp2 :=
  fp2fromfp (
    fp_zero).



Definition fp2neg (n_3 : fp2) : fp2 :=
  let (n1_4, n2_5) := n_3 in
  (
    (
      fp_zero) - (
      n1_4),
    (
      fp_zero) - (
      n2_5)
  ).

Definition fp2add (n_6 : fp2) (m_7 : fp2) : fp2 :=
  let (n1_8, n2_9) := n_6 in
  let (m1_10, m2_11) := m_7 in
  ((n1_8) + (m1_10), (n2_9) + (m2_11)).

Definition fp2sub (n_12 : fp2) (m_13 : fp2) : fp2 :=
  fp2add (n_12) (fp2neg (m_13)).

Definition fp2mul (n_14 : fp2) (m_15 : fp2) : fp2 :=
  let (n1_16, n2_17) := n_14 in
  let (m1_18, m2_19) := m_15 in
  let x1_20 := ((n1_16) * (m1_18)) - ((n2_17) * (m2_19)) in
  let x2_21 := ((n1_16) * (m2_19)) + ((n2_17) * (m1_18)) in
  (x1_20, x2_21).


Definition fp2inv (n_22 : fp2) : fp2 :=
  let (n1_23, n2_24) := n_22 in
  let t0_25 := ((n1_23) * (n1_23)) + ((n2_24) * (n2_24)) in
  let t1_26 :=
    fp_inv (
      t0_25)
  in
  let x1_27 := (n1_23) * (t1_26) in
  let x2_28 :=
    (
      fp_zero) - (
      (n2_24) * (t1_26))
  in
  (x1_27, x2_28).

Definition fp2conjugate (n_29 : fp2) : fp2 :=
  let (n1_30, n2_31) := n_29 in
  (
    n1_30,
    (
      fp_zero) - (
      n2_31)
  ).

Definition fp6fromfp2 (n_32 : fp2) : fp6 :=
  (n_32, fp2zero, fp2zero).

Definition fp6zero : fp6 :=
  fp6fromfp2 (fp2zero).

Definition fp6neg (n_33 : fp6) : fp6 :=
  let '(n1_34, n2_35, n3_36) := n_33 in
  (
    fp2sub (fp2zero) (n1_34),
    fp2sub (fp2zero) (n2_35),
    fp2sub (fp2zero) (n3_36)
  ).

Definition fp6add (n_37 : fp6) (m_38 : fp6) : fp6 :=
  let '(n1_39, n2_40, n3_41) := n_37 in
  let '(m1_42, m2_43, m3_44) := m_38 in
  (fp2add (n1_39) (m1_42), fp2add (n2_40) (m2_43), fp2add (n3_41) (m3_44)).

Definition fp6sub (n_45 : fp6) (m_46 : fp6) : fp6 :=
  fp6add (n_45) (fp6neg (m_46)).

Definition fp6mul (n_47 : fp6) (m_48 : fp6) : fp6 :=
  let '(n1_49, n2_50, n3_51) := n_47 in
  let '(m1_52, m2_53, m3_54) := m_48 in
  let eps_55 :=
    (
      fp_one,
      fp_one
    )
  in
  let t1_56 := fp2mul (n1_49) (m1_52) in
  let t2_57 := fp2mul (n2_50) (m2_53) in
  let t3_58 := fp2mul (n3_51) (m3_54) in
  let t4_59 := fp2mul (fp2add (n2_50) (n3_51)) (fp2add (m2_53) (m3_54)) in
  let t5_60 := fp2sub (fp2sub (t4_59) (t2_57)) (t3_58) in
  let x_61 := fp2add (fp2mul (t5_60) (eps_55)) (t1_56) in
  let t4_62 := fp2mul (fp2add (n1_49) (n2_50)) (fp2add (m1_52) (m2_53)) in
  let t5_63 := fp2sub (fp2sub (t4_62) (t1_56)) (t2_57) in
  let y_64 := fp2add (t5_63) (fp2mul (eps_55) (t3_58)) in
  let t4_65 := fp2mul (fp2add (n1_49) (n3_51)) (fp2add (m1_52) (m3_54)) in
  let t5_66 := fp2sub (fp2sub (t4_65) (t1_56)) (t3_58) in
  let z_67 := fp2add (t5_66) (t2_57) in
  (x_61, y_64, z_67).

Definition fp6inv (n_68 : fp6) : fp6 :=
  let '(n1_69, n2_70, n3_71) := n_68 in
  let eps_72 :=
    (
      fp_one,
      fp_one
    )
  in
  let t1_73 := fp2mul (n1_69) (n1_69) in
  let t2_74 := fp2mul (n2_70) (n2_70) in
  let t3_75 := fp2mul (n3_71) (n3_71) in
  let t4_76 := fp2mul (n1_69) (n2_70) in
  let t5_77 := fp2mul (n1_69) (n3_71) in
  let t6_78 := fp2mul (n2_70) (n3_71) in
  let x0_79 := fp2sub (t1_73) (fp2mul (eps_72) (t6_78)) in
  let y0_80 := fp2sub (fp2mul (eps_72) (t3_75)) (t4_76) in
  let z0_81 := fp2sub (t2_74) (t5_77) in
  let t0_82 := fp2mul (n1_69) (x0_79) in
  let t0_83 := fp2add (t0_82) (fp2mul (eps_72) (fp2mul (n3_71) (y0_80))) in
  let t0_84 := fp2add (t0_83) (fp2mul (eps_72) (fp2mul (n2_70) (z0_81))) in
  let t0_85 := fp2inv (t0_84) in
  let x_86 := fp2mul (x0_79) (t0_85) in
  let y_87 := fp2mul (y0_80) (t0_85) in
  let z_88 := fp2mul (z0_81) (t0_85) in
  (x_86, y_87, z_88).

Definition fp12fromfp6 (n_89 : fp6) : fp12 :=
  (n_89, fp6zero).

Definition fp12neg (n_90 : fp12) : fp12 :=
  let '(n1_91, n2_92) := n_90 in
  (fp6sub (fp6zero ) (n1_91), fp6sub (fp6zero ) (n2_92)).

Definition fp12add (n_93 : fp12) (m_94 : fp12) : fp12 :=
  let '(n1_95, n2_96) := n_93 in
  let '(m1_97, m2_98) := m_94 in
  (fp6add (n1_95) (m1_97), fp6add (n2_96) (m2_98)).

Definition fp12sub (n_99 : fp12) (m_100 : fp12) : fp12 :=
  fp12add (n_99) (fp12neg (m_100)).

Definition fp12mul (n_101 : fp12) (m_102 : fp12) : fp12 :=
  let '(n1_103, n2_104) := n_101 in
  let '(m1_105, m2_106) := m_102 in
  let gamma_107 :=
    (
      fp2zero,
      fp2fromfp (
        fp_one),
      fp2zero
    )
  in
  let t1_108 := fp6mul (n1_103) (m1_105) in
  let t2_109 := fp6mul (n2_104) (m2_106) in
  let x_110 := fp6add (t1_108) (fp6mul (t2_109) (gamma_107)) in
  let y_111 := fp6mul (fp6add (n1_103) (n2_104)) (fp6add (m1_105) (m2_106)) in
  let y_112 := fp6sub (fp6sub (y_111) (t1_108)) (t2_109) in
  (x_110, y_112).

Definition fp12inv (n_113 : fp12) : fp12 :=
  let '(n1_114, n2_115) := n_113 in
  let gamma_116 :=
    (
      fp2zero,
      fp2fromfp (
        fp_one),
      fp2zero
    )
  in
  let t1_117 := fp6mul (n1_114) (n1_114) in
  let t2_118 := fp6mul (n2_115) (n2_115) in
  let t1_119 := fp6sub (t1_117) (fp6mul (gamma_116) (t2_118)) in
  let t2_120 := fp6inv (t1_119) in
  let x_121 := fp6mul (n1_114) (t2_120) in
  let y_122 := fp6neg (fp6mul (n2_115) (t2_120)) in
  (x_121, y_122).

Definition fp_to_nat (n : fp) : nat := val prime n.

Coercion fp_to_nat : fp >-> nat.



Definition fp12exp (n_123 : fp12) (k_124 : scalar) : fp12 :=
  let l_125 := N.sub (usize 255) (most_significant_bit (k_124) (usize 255)) in
  let c_126 := n_123 in
  let '(c_126) :=
    foldi (l_125) (usize 255) (fun i_127 c_126 =>
      let c_126 := fp12mul (c_126) (c_126) in
      let '(c_126) :=
        if nat_bit (
          256) (
          k_124) ((N.sub (N.sub (usize 255) (i_127)) (usize 1))) then (
          let c_126 := fp12mul (c_126) (n_123) in
          (c_126)
        ) else ( (c_126)
        )
      in
      (c_126))
    (c_126)
  in
  c_126.

Definition fp12conjugate (n_128 : fp12) : fp12 :=
  let '(n1_129, n2_130) := n_128 in
  (n1_129, fp6neg (n2_130)).

Definition fp12zero  : fp12 :=
  fp12fromfp6 (fp6zero ).

Definition g1add_a (p_131 : g1) (q_132 : g1) : g1 :=
  let '(x1_133, y1_134, _) := p_131 in
  let '(x2_135, y2_136, _) := q_132 in
  let x_diff_137 := (x2_135) - (x1_133) in
  let y_diff_138 := (y2_136) - (y1_134) in
  let xovery_139 :=
    (y_diff_138) * (
      fp_inv (
        x_diff_137))
  in
  let x3_140 :=
    (
      (
        fp_exp (
          xovery_139) (pub_u32 2)) - (x1_133)) - (x2_135)
  in
  let y3_141 := ((xovery_139) * ((x1_133) - (x3_140))) - (y1_134) in
  (x3_140, y3_141, false).

Definition g1double_a (p_142 : g1) : g1 :=
  let '(x1_143, y1_144, _) := p_142 in
  let x12_145 :=
    fp_exp (
      x1_143) (pub_u32 2)
  in
  let xovery_146 :=
    ((fp_three) * (x12_145)) * (
      fp_inv ((fp_two  * (y1_144)))) in
  let x3_147 :=
    (
      fp_exp (
        xovery_146) (pub_u32 2)) - (
      (
        fp_two  * (
        x1_143)))
  in
  let y3_148 := ((xovery_146) * ((x1_143) - (x3_147))) - (y1_144) in
  (x3_147, y3_148, false).


(* Self written definition *)
Definition g1_eqb (x y: g1): bool := 
  let '(x1, x2, xinf) := x in
  let '(y1, y2, yinf) := y in
  fp_eqb x1 y1 && fp_eqb x2 y2 && Bool.eqb xinf yinf.


Definition g1double (p_157 : g1) : g1 :=
  let '(x1_158, y1_159, inf1_160) := p_157 in
  if (
    (negb (fp_eqb
       (y1_159) (
        fp_zero))) && (
      negb (inf1_160))) then (g1double_a (p_157)) else (
    (
      fp_zero,
      fp_zero,
      true
    )).

Definition g1add (p_149 : g1) (q_150 : g1) : g1 :=
  let '(x1_151, y1_152, inf1_153) := p_149 in
  let '(x2_154, y2_155, inf2_156) := q_150 in
  if (inf1_153) then (q_150) else (
    if (inf2_156) then (p_149) else (
      if (g1_eqb (p_149) (q_150)) then (g1double (p_149)) else (
        if (
          negb (
            (fp_eqb (x1_151) (x2_154)) && (
              fp_eqb (y1_152)  (
                (
                  fp_zero) - (
                  y2_155))))) then (g1add_a (p_149) (q_150)) else (
          (
            fp_zero,
            fp_zero,
            true
          ))))).



Definition g1mul (m_161 : scalar) (p_162 : g1) : g1 :=
  let n_163 := usize 255 in
  let k_164 := N.sub (n_163) (most_significant_bit (m_161) (n_163)) in
  let t_165 := p_162 in
  let '(t_165) :=
    foldi (k_164) (n_163) (fun i_166 t_165 =>
      let t_165 := g1double (t_165) in
      let '(t_165) :=
        if nat_bit (
          256) (
          m_161) (N.sub (N.sub (n_163) (i_166)) (usize 1)) then (
          let t_165 := g1add (t_165) (p_162) in
          (t_165)
        ) else ( (t_165)
        )
      in
      (t_165))
    (t_165)
  in
  t_165.

Definition g1neg (p_167 : g1) : g1 :=
  let '(x_168, y_169, inf_170) := p_167 in
  (
    x_168,
    (
      fp_zero) - (
      y_169),
    inf_170
  ).

Definition g2add_a (p_171 : g2) (q_172 : g2) : g2 :=
  let '(x1_173, y1_174, _) := p_171 in
  let '(x2_175, y2_176, _) := q_172 in
  let x_diff_177 := fp2sub (x2_175) (x1_173) in
  let y_diff_178 := fp2sub (y2_176) (y1_174) in
  let xovery_179 := fp2mul (y_diff_178) (fp2inv (x_diff_177)) in
  let t1_180 := fp2mul (xovery_179) (xovery_179) in
  let t2_181 := fp2sub (t1_180) (x1_173) in
  let x3_182 := fp2sub (t2_181) (x2_175) in
  let t1_183 := fp2sub (x1_173) (x3_182) in
  let t2_184 := fp2mul (xovery_179) (t1_183) in
  let y3_185 := fp2sub (t2_184) (y1_174) in
  (x3_182, y3_185, false).

Definition g2double_a (p_186 : g2) : g2 :=
  let '(x1_187, y1_188, _) := p_186 in
  let x12_189 := fp2mul (x1_187) (x1_187) in
  let t1_190 :=
    fp2mul (
      fp2fromfp (
        fp_three)) (x12_189)
  in
  let t2_191 :=
    fp2inv (
      fp2mul (
        fp2fromfp fp_two) (y1_188))
  in
  let xovery_192 := fp2mul (t1_190) (t2_191) in
  let t1_193 := fp2mul (xovery_192) (xovery_192) in
  let t2_194 :=
    fp2mul (
      fp2fromfp (
        fp_two )) (
      x1_187)
  in
  let x3_195 := fp2sub (t1_193) (t2_194) in
  let t1_196 := fp2sub (x1_187) (x3_195) in
  let t2_197 := fp2mul (xovery_192) (t1_196) in
  let y3_198 := fp2sub (t2_197) (y1_188) in
  (x3_195, y3_198, false).

(* TODO *)
(* Self written definition *)
Definition fp2_eqb (x y: fp2) := 
  let (x1, x2) := x in 
  let (y1, y2) := y in
  fp_eqb x1 y1 && fp_eqb x2 y2.
Definition g2_eqb (x y: g2): bool := 
  let '(x1, x2, xinf) := x in
  let '(y1, y2, yinf) := y in
  fp2_eqb x1 y1 && fp2_eqb x2 y2 && Bool.eqb xinf yinf.

Definition g2double (p_207 : g2) : g2 :=
  let '(x1_208, y1_209, inf1_210) := p_207 in
  if (negb (fp2_eqb (y1_209)  (fp2zero)) && (negb (inf1_210))) then (
    g2double_a (p_207)) else ((fp2zero, fp2zero, true)).

Definition g2add (p_199 : g2) (q_200 : g2) : g2 :=
  let '(x1_201, y1_202, inf1_203) := p_199 in
  let '(x2_204, y2_205, inf2_206) := q_200 in
  if (inf1_203) then (q_200) else (
    if (inf2_206) then (p_199) else (
      if (g2_eqb (p_199) (q_200)) then (g2double (p_199)) else (
        if (
          negb (
            (fp2_eqb (x1_201) (x2_204)) && (fp2_eqb (y1_202) (fp2neg (y2_205))))) then (
          g2add_a (p_199) (q_200)) else ((fp2zero, fp2zero, true))))).



Definition g2mul (m_211 : scalar) (p_212 : g2) : g2 :=
  let n_213 := usize 255 in
  let k_214 := N.sub (n_213) (most_significant_bit (m_211) (n_213)) in
  let t_215 := p_212 in
  let '(t_215) :=
    foldi (k_214) (n_213) (fun i_216 t_215 =>
      let t_215 := g2double (t_215) in
      let '(t_215) :=
        if nat_bit (
          256) (
          m_211) (N.sub (N.sub (n_213) (i_216)) (usize 1)) then (
          let t_215 := g2add (t_215) (p_212) in
          (t_215)
        ) else ( (t_215)
        )
      in
      (t_215))
    (t_215)
  in
  t_215.

Definition g2neg (p_217 : g2) : g2 :=
  let '(x_218, y_219, inf_220) := p_217 in
  (x_218, fp2neg (y_219), inf_220).

Definition twist (p_221 : g1) : (fp12 * fp12) :=
  let '(p0_222, p1_223, _) := p_221 in
  let x_224 := ((fp2zero, fp2fromfp (p0_222), fp2zero), fp6zero ) in
  let y_225 := (fp6zero , (fp2zero, fp2fromfp (p1_223), fp2zero)) in
  (x_224, y_225).

Definition line_double_p (r_226 : g2) (p_227 : g1) : fp12 :=
  let '(r0_228, r1_229, _) := r_226 in
  let a_230 :=
    fp2mul (
      fp2fromfp (
        fp_three)) (fp2mul (r0_228) (r0_228))
  in
  let a_231 :=
    fp2mul (a_230) (
      fp2inv (
        fp2mul (
          fp2fromfp (
            fp_two )) (
          r1_229)))
  in
  let b_232 := fp2sub (r1_229) (fp2mul (a_231) (r0_228)) in
  let a_233 := fp12fromfp6 (fp6fromfp2 (a_231)) in
  let b_234 := fp12fromfp6 (fp6fromfp2 (b_232)) in
  let '(x_235, y_236) := twist (p_227) in
  fp12neg (fp12sub (fp12sub (y_236) (fp12mul (a_233) (x_235))) (b_234)).

Definition line_add_p (r_237 : g2) (q_238 : g2) (p_239 : g1) : fp12 :=
  let '(r0_240, r1_241, _) := r_237 in
  let '(q0_242, q1_243, _) := q_238 in
  let a_244 :=
    fp2mul (fp2sub (q1_243) (r1_241)) (fp2inv (fp2sub (q0_242) (r0_240)))
  in
  let b_245 := fp2sub (r1_241) (fp2mul (a_244) (r0_240)) in
  let a_246 := fp12fromfp6 (fp6fromfp2 (a_244)) in
  let b_247 := fp12fromfp6 (fp6fromfp2 (b_245)) in
  let '(x_248, y_249) := twist (p_239) in
  fp12neg (fp12sub (fp12sub (y_249) (fp12mul (a_246) (x_248))) (b_247)).

(* TODO *)
Axiom array_to_le_bytes : forall {l}, lseq N l  -> fp.

Definition frobenius (f_250 : fp12) : fp12 :=
  let '((g0_251, g1_252, g2_253), (h0_254, h1_255, h2_256)) := f_250 in
  let t1_257 := fp2conjugate (g0_251) in
  let t2_258 := fp2conjugate (h0_254) in
  let t3_259 := fp2conjugate (g1_252) in
  let t4_260 := fp2conjugate (h1_255) in
  let t5_261 := fp2conjugate (g2_253) in
  let t6_262 := fp2conjugate (h2_256) in
  let c1_263 :=
    array_from_list (
      let l :=
        [
          secret (pub_u64 10162220747404304312);
          secret (pub_u64 17761815663483519293);
          secret (pub_u64 8873291758750579140);
          secret (pub_u64 1141103941765652303);
          secret (pub_u64 13993175198059990303);
          secret (pub_u64 1802798568193066599)
        ]
      in l)
  in
  let c1_264 := array_to_le_bytes (c1_263) in
  let c1_265 := c1_264 in
  let c2_266 :=
    array_from_list (
      let l :=
        [
          secret (pub_u64 3240210268673559283);
          secret (pub_u64 2895069921743240898);
          secret (pub_u64 17009126888523054175);
          secret (pub_u64 6098234018649060207);
          secret (pub_u64 9865672654120263608);
          secret (pub_u64 71000049454473266)
        ]
      in l)
  in
  let c2_267 := array_to_le_bytes (c2_266) in
  let c2_268 := c2_267
  in
  let gamma11_269 := (c1_265, c2_268) in
  let gamma12_270 := fp2mul (gamma11_269) (gamma11_269) in
  let gamma13_271 := fp2mul (gamma12_270) (gamma11_269) in
  let gamma14_272 := fp2mul (gamma13_271) (gamma11_269) in
  let gamma15_273 := fp2mul (gamma14_272) (gamma11_269) in
  let t2_274 := fp2mul (t2_258) (gamma11_269) in
  let t3_275 := fp2mul (t3_259) (gamma12_270) in
  let t4_276 := fp2mul (t4_260) (gamma13_271) in
  let t5_277 := fp2mul (t5_261) (gamma14_272) in
  let t6_278 := fp2mul (t6_262) (gamma15_273) in
  ((t1_257, t3_275, t5_277), (t2_274, t4_276, t6_278)).

Import nat_mod_256.
Infix "/" := divs.

Definition final_exponentiation (f_279 : fp12) : fp12 :=
  let fp6_280 := fp12conjugate (f_279) in
  let finv_281 := fp12inv (f_279) in
  let fp6_1_282 := fp12mul (fp6_280) (finv_281) in
  let fp8_283 := frobenius (frobenius (fp6_1_282)) in
  let f_284 := fp12mul (fp8_283) (fp6_1_282) in
  let u_285 :=
    repr (
      pub_u128 15132376222941642752)
  in
  let t0_286 := fp12mul (f_284) (f_284) in
  let t1_287 := fp12exp (t0_286) (u_285) in
  let t1_288 := fp12conjugate (t1_287) in
  let t2_289 :=
    fp12exp (t1_288) (
      (u_285) / (
        (repr 2)))
  in
  let t2_290 := fp12conjugate (t2_289) in
  let t3_291 := fp12conjugate (f_284) in
  let t1_292 := fp12mul (t3_291) (t1_288) in
  let t1_293 := fp12conjugate (t1_292) in
  let t1_294 := fp12mul (t1_293) (t2_290) in
  let t2_295 := fp12exp (t1_294) (u_285) in
  let t2_296 := fp12conjugate (t2_295) in
  let t3_297 := fp12exp (t2_296) (u_285) in
  let t3_298 := fp12conjugate (t3_297) in
  let t1_299 := fp12conjugate (t1_294) in
  let t3_300 := fp12mul (t1_299) (t3_298) in
  let t1_301 := fp12conjugate (t1_299) in
  let t1_302 := frobenius (frobenius (frobenius (t1_301))) in
  let t2_303 := frobenius (frobenius (t2_296)) in
  let t1_304 := fp12mul (t1_302) (t2_303) in
  let t2_305 := fp12exp (t3_300) (u_285) in
  let t2_306 := fp12conjugate (t2_305) in
  let t2_307 := fp12mul (t2_306) (t0_286) in
  let t2_308 := fp12mul (t2_307) (f_284) in
  let t1_309 := fp12mul (t1_304) (t2_308) in
  let t2_310 := frobenius (t3_300) in
  let t1_311 := fp12mul (t1_309) (t2_310) in
  t1_311.

Definition pairing (p_312 : g1) (q_313 : g2) : fp12 :=
  let t_314 :=
    repr (
      pub_u128 15132376222941642752)
  in
  let r_315 := q_313 in
  let f_316 :=
    fp12fromfp6 (
      fp6fromfp2 (
        fp2fromfp (
          fp_one)))
  in
  let '(r_315, f_316) :=
    foldi (usize 1) (usize 64) (fun i_317 '(r_315, f_316) =>
      let lrr_318 := line_double_p (r_315) (p_312) in
      let r_315 := g2double (r_315) in
      let f_316 := fp12mul (fp12mul (f_316) (f_316)) (lrr_318) in
      let (r_315, f_316) :=
        if nat_bit (256) (
          t_314) (N.sub (N.sub (usize 64) (i_317)) (usize 1)) then (
          let lrq_319 := line_add_p (r_315) (q_313) (p_312) in
          let r_315 := g2add (r_315) (q_313) in
          let f_316 := fp12mul (f_316) (lrq_319) in
          (r_315, f_316)
        ) else ( (r_315, f_316)
        )
      in
      (r_315, f_316))
    (r_315, f_316)
  in
  final_exponentiation (fp12conjugate (f_316)).

(* ########### PROOF SECTION ########### *)


Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Algebra.Field Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Decidable Crypto.Util.Tactics.DestructHead Crypto.Util.Tactics.BreakMatch.
Require Import blsprime.
Require Import Ring.
Require Export Ring_theory.
Require Import Setoid.

(* Equality between fp elements *)
Definition fp_eq (x y: fp): Prop := x = y.
Lemma fp_eq_ok: forall x y, (x = y) <-> fp_eq x y.
Proof. reflexivity.
Qed.

(* Checking if a point is actually on the curve - since FC points are only defined as points on the curve, and our points are everyting from (fp, fp), this is needed *)
Definition g1_on_curve (p:g1) := let '(x, y, inf) := p in if inf then True else y*y=x*x*x + fp_four.

(* Checking equivalence between two points in G1. First check is if they're pointAtInfinity, and if not, then check coordinates *)
Definition g1_eq (x y: g1) := 
  let '(x1, x2, xinf) := x in
  let '(y1, y2, yinf) := y in
  if xinf then yinf = true else
    x1 = y1 /\ x2 = y2.

Lemma fp_same_if_eq: forall x y, fp_eqb x y = true <-> x = y.
Proof. intros x y. split.
  - unfold fp_eqb. intros H. apply Z.eqb_eq in H. destruct x. destruct y. simpl in H. apply (zirr prime val val0 inZnZ inZnZ0 H).
  - intros H. apply znz_inj in H. apply Z.eqb_eq in H. apply H. 
Qed.

Lemma fp_eq_true: forall x, fp_eqb x x = true.
Proof. intros x. unfold fp_eqb. apply Z.eqb_refl. 
Qed.

(* If the boolean equality is the same, then the elements are the same *)
Lemma same_if_g1_eq: forall x y, g1_eqb x y = true -> g1_eq x y.
Proof. intros x y. unfold g1_eqb, g1_eq. destruct x. destruct y. destruct p. destruct p0. intros H.
destruct b.
- destruct (fp_eqb f f1); destruct (fp_eqb f0 f2); destruct b0; try reflexivity; try inversion H.
- destruct (fp_eqb f f1) eqn:E; destruct (fp_eqb f0 f2) eqn:E1; destruct b0; try reflexivity; try inversion H.
  apply fp_same_if_eq in E. apply fp_same_if_eq in E1. split. apply E. apply E1.
Qed.

(* Every element is equal itself *)
Lemma g1_eqb_true: forall p, g1_eqb p p = true.
Proof. intros p. unfold g1_eqb. destruct p. destruct p. repeat rewrite fp_eq_true. rewrite Bool.eqb_reflx. reflexivity.
Qed.

Require Import Coq.setoid_ring.Field.

Lemma fp_field_theory: field_theory fp_zero fp_one fp_add fp_mul fp_sub fp_neg fp_div fp_inv fp_eq.
Proof. apply (FZpZ prime blsprime). Qed.

Add Field fp_field: fp_field_theory.

(* Fiat-crypto field from standard library field *)
Instance fp_fc_field : @field fp fp_eq fp_zero fp_one fp_neg fp_add fp_sub fp_mul fp_inv fp_div.
Proof.
  repeat split; try apply (Fdiv_def fp_field_theory); try (intros ; field); try apply (_ (fp_field_theory)); auto.
  - symmetry; apply (F_1_neq_0 (fp_field_theory)).
Qed.

Lemma g1_dec: DecidableRel fp_eq.
Proof. unfold Decidable. unfold fp_eq. intros x y. generalize (fp_same_if_eq x y). intros H. destruct (fp_eqb x y).
  - left. apply H. reflexivity. 
  - right. apply not_iff_compat in H. apply H. congruence.
Qed.

Lemma pos_le_three: forall pos: positive, (pos < 3)%positive -> pos = 1%positive \/ pos = 2%positive.
Proof. intros pos. destruct pos.
- intros H. inversion H. unfold Pos.compare, Pos.compare_cont in H1. destruct pos; inversion H1.
- intros H. assert (pos = 1%positive). inversion H. unfold Pos.compare, Pos.compare_cont in H1. destruct pos; inversion H1. reflexivity.
  rewrite H0. right. reflexivity.
- intros H. left. reflexivity.
Qed.

About Ring.char_ge.

Lemma fp_char_ge:  @Ring.char_ge fp fp_eq fp_zero fp_one fp_neg fp_add fp_sub fp_mul (BinNat.N.succ_pos BinNat.N.two).
Proof. 
  unfold char_ge. unfold Hierarchy.char_ge. intros pos. simpl. intros H. unfold fp_eq. apply pos_le_three in H. destruct H;
  rewrite H; simpl; intro c; discriminate c.
Qed.

(* Representation af a Fiat-crypto G1 point *)
Definition g1_fc_point := @W.point fp fp_eq fp_add fp_mul fp_zero fp_four. 
(* Fiat-Crypto Equivalence, Addition and Zero element *)
Definition g1_fc_eq := @W.eq fp fp_eq fp_add fp_mul fp_zero fp_four.       
Definition g1_fc_add (p1 p2 :g1_fc_point ) :g1_fc_point := @W.add fp fp_eq fp_zero fp_one fp_neg fp_add fp_sub fp_mul fp_inv fp_div fp_fc_field g1_dec fp_char_ge fp_zero fp_four p1 p2.
Definition g1_fc_zero := @W.zero fp fp_eq fp_add fp_mul fp_zero fp_four.

(* ?x? is x performed by hacspec. #x# is x performed by Fiat-Crypto *)
Infix "?+?" := g1add (at level 81).
Infix "?=?" := g1_eq (at level 100).
Infix "#+#" := g1_fc_add (at level 81).
Infix "#=#" := g1_fc_eq (at level 100).

(* Checking the Fiat-Crypto functions actually work*)
Example add_zero_is_zero_in_fc: (g1_fc_zero #+# g1_fc_zero) #=# g1_fc_zero.
Proof. reflexivity.
Qed.

(* Translating Fiat-Crypto Point Representations to our G1 points (x, y, isPointAtInfinity) *)
Definition g1_from_fc (p: g1_fc_point): g1 := 
  match W.coordinates p with
  | inr tt => (fp_zero, fp_zero, true)
  | inl (pair x y) => (x, y, false)
  end.


(* Translating our points to Fiat-Crypto Points *)
Program Definition g1_to_fc (p: g1): g1_fc_point :=
    match p return fp*fp+unit with
    | (_, _, true) => inr tt
    | (x, y, false) => if fp_eqb (y*y) (x*x*x + fp_four) 
      then inl (x, y) 
      else inr tt
    end.
    Next Obligation.
    Crypto.Util.Tactics.BreakMatch.break_match. 
    - trivial. 
    - unfold fp_eqb in Heqb. apply fp_same_if_eq in Heqb. rewrite Heqb. field. 
    - trivial.
    Qed.


Lemma algebra_helper_1: forall x y z, x - y = z <-> x = y + z.
Proof. intros x y z. split.
  - intros H. rewrite <- H. rewrite fp_eq_ok. field. 
  - intros H. rewrite H. rewrite fp_eq_ok. field.
Qed.

Lemma sub_eq_zero_means_same: forall x y, x - y = fp_zero <-> x = y.
Proof. split. 
  - intros H. apply algebra_helper_1 in H. rewrite H. rewrite fp_eq_ok. field.
  - intros H. rewrite H. rewrite fp_eq_ok. field. 
Qed.

(* Integral domain to help with som algebraic properties *)
Definition fp_integral_domain := @Field.integral_domain fp fp_eq fp_zero fp_one fp_neg fp_add fp_mul fp_sub fp_inv fp_div fp_fc_field g1_dec.

Definition nonzero_iff := @IntegralDomain.IntegralDomain.nonzero_product_iff_nonzero_factors fp fp_eq fp_zero fp_one fp_neg fp_add fp_sub fp_mul fp_integral_domain.

Lemma double_negation: forall p: Prop, p -> ~~p.
Proof. intros P H H1. contradiction. Qed. 

Lemma fp_neg_invo: forall x, fp_neg (fp_neg x) = x. 
Proof. intros x.  rewrite fp_eq_ok. field. Qed. 

Lemma negation_eq_implies_zero: forall x, fp_eq x (fp_neg x) -> x = fp_zero.
Proof. intros x H. unfold fp_eq in H. generalize fp_field_theory. intros [[]].
  rewrite <- (Radd_0_l (fp_neg x)) in H. rewrite Radd_comm in H.
  rewrite <- algebra_helper_1 in H.
  rewrite Rsub_def in H.
  rewrite <- fp_neg_invo.
  assert (x + x = fp_two * x). {  rewrite fp_eq_ok. unfold fp_two. field. }
  rewrite fp_neg_invo in H. rewrite H0 in H. generalize (nonzero_iff fp_two x). intros H1. apply not_iff_compat in H1. destruct H1.
  unfold fp_eq in H2. apply double_negation in H. apply H1 in H. apply Classical_Prop.not_and_or in H. destruct H.
  - destruct H. intros c. discriminate c.
  - apply Classical_Prop.NNPP in H. rewrite H. rewrite fp_neg_invo. reflexivity.
Qed.

Lemma square_law: forall x y, x * x - y * y = (x + y) * (x - y).
Proof. intros x y. rewrite fp_eq_ok. field. 
Qed.

Lemma symmetrical_x_axis: forall x1 y1 x2 y2, g1_on_curve (x1, y1, false) -> g1_on_curve (x2, y2, false) -> x1 = x2 -> y1 = y2 \/ y1 = fp_neg y2.
Proof. intros x1 y1 x2 y2 H1 H2 H3. generalize (nonzero_iff (y1 + y2) (y1 - y2)). intro H4.
  unfold g1_on_curve in H1. unfold g1_on_curve in H2. rewrite <- H3 in H2. rewrite <- H2 in H1. apply sub_eq_zero_means_same in H1. rewrite square_law in H1.
  apply not_iff_compat in H4. rewrite H1 in H4. unfold fp_eq in H4. destruct H4. 
  (generalize fp_field_theory). intros [[]]. apply Classical_Prop.not_and_or in H. 
  - destruct H.
    + right. apply sub_eq_zero_means_same. rewrite Rsub_def. rewrite fp_neg_invo. apply Classical_Prop.NNPP. apply H.
    + left. apply sub_eq_zero_means_same. apply Classical_Prop.NNPP. apply H.
  - congruence.
Qed.

(* Admitted because weird compilation (wordsize is weird) *)
Lemma exp2ismul: forall x, fp_exp x (pub_u32 2) = x * x.
Proof. reflexivity. Qed. 



(* The equivalence proof. If two points are on the curve, adding them together using hacspec is the same as converting to fiat-crypto, adding them and converting back *)
Lemma g1_addition_equal: forall p q: g1, g1_on_curve p -> g1_on_curve q -> (p ?+? q) ?=? (g1_from_fc ((g1_to_fc p) #+# (g1_to_fc q))). 
Proof. Opaque g1_eqb. intros p q H H0. unfold g1add. destruct p. destruct p. destruct q. 
  unfold g1_from_fc, g1_to_fc, g1_fc_add. destruct p. unfold g1_eq. simpl. 
  (generalize fp_field_theory). intros [[]].
  destruct b eqn:E.
  - destruct b0 eqn:E1.
    + reflexivity.
    + unfold g1_on_curve in H0. rewrite <- H0. rewrite fp_eq_true. split. reflexivity. reflexivity.
  - destruct b0 eqn:E1.
    + unfold g1_on_curve in H. rewrite <- H. rewrite fp_eq_true. split. reflexivity. reflexivity.
    + unfold g1_on_curve in H. unfold g1_on_curve in H0. rewrite H0. rewrite H. rewrite fp_eq_true. rewrite fp_eq_true.
      destruct (g1_eqb (f, f0, false) (f1, f2, false)) eqn:E2. 
      * simpl. destruct (fp_eqb f0 fp_zero) eqn:E3. 
        --  simpl. apply same_if_g1_eq in E2. unfold g1_eq in E2. destruct E2. rewrite H1. unfold fp_eq. unfold dec. destruct (g1_dec f1 f1) eqn:E6. 
          ++ destruct (g1_dec f2 (fp_neg f0)).
            ** simpl. reflexivity.
            ** exfalso. rewrite <- H2 in n. apply fp_same_if_eq in E3. rewrite E3 in n. destruct n. reflexivity.
          ++ exfalso. destruct n. reflexivity.
        -- simpl. apply same_if_g1_eq in E2. simpl in E2. destruct E2. destruct (dec (fp_eq f f1)).
          ++ destruct (dec (fp_eq f2 (fp_neg f0))).
            ** exfalso. rewrite <- H2 in f4. apply negation_eq_implies_zero in f4. rewrite f4 in E3. rewrite fp_eq_true in E3. discriminate E3.
            ** repeat rewrite exp2ismul. split.
              --- rewrite fp_eq_ok. rewrite H1. unfold fp_three. unfold fp_two. field. split.
                +++ unfold fp_eq. intros c. rewrite c in E3. rewrite fp_eq_true in E3. discriminate E3.
                +++ unfold fp_eq. intros c. discriminate c.
              --- unfold fp_three. unfold fp_two. rewrite fp_eq_ok. rewrite H1. field. split. 
                +++ unfold fp_eq. intros c. rewrite c in E3. rewrite fp_eq_true in E3. discriminate E3.
                +++ unfold fp_eq. intros c. discriminate c.
          ++ rewrite H1 in n. destruct n. reflexivity.
      * destruct (fp_eqb f f1) eqn:E3.
        -- destruct (fp_eqb f0 (fp_zero - f2)) eqn:E4.
          ++ simpl. destruct (dec (fp_eq f f1)).
            ** destruct (dec (fp_eq f2 (fp_neg f0))).
              --- reflexivity.
              --- exfalso. apply fp_same_if_eq in E4. rewrite E4 in n. destruct n. rewrite Rsub_def. rewrite Radd_0_l. rewrite fp_neg_invo. reflexivity.
            ** exfalso. destruct n. unfold fp_eq. apply (fp_same_if_eq _ _). apply E3.
          ++ exfalso. generalize (symmetrical_x_axis f f0 f1 f2 H H0). apply fp_same_if_eq in E3. intros c. apply c in E3 as H7. destruct H7.
            ** rewrite E3 in E2. rewrite H1 in E2. rewrite g1_eqb_true in E2. discriminate.
            ** rewrite H1 in E4. rewrite Rsub_def in E4. rewrite Radd_0_l in E4. rewrite fp_eq_true in E4. discriminate E4.
        -- simpl. destruct (dec (fp_eq f f1)).
          ++ exfalso. unfold fp_eq in f3. rewrite f3 in E3. rewrite fp_eq_true in E3. discriminate E3.
          ++ rewrite exp2ismul. split;
            rewrite fp_eq_ok; field; unfold fp_eq; intros H1; rewrite sub_eq_zero_means_same in H1; rewrite H1 in E3; rewrite fp_eq_true in E3; discriminate E3.
Qed.

  

(* fp2 ring/field stuff*)



Definition fp2one := (fp_one, fp_zero).

Definition fp2eq (x y:fp2) := x = y.

Lemma fp2eq_ok: forall x y, x = y <-> fp2eq x y.
Proof. intros x y. reflexivity.
Qed.

Lemma fp2_ring_theory: ring_theory fp2zero fp2one fp2add fp2mul fp2sub fp2neg fp2eq.
Proof. split; intros; unfold fp2eq, fp2add, fp2zero, fp2one, fp2mul, fp2sub, fp2sub, fp2neg, fp2fromfp; try destruct x; try destruct y; try destruct z; apply pair_equal_spec; split; rewrite fp_eq_ok; field.
Qed.

Add Ring fp2_ring: fp2_ring_theory.

Definition fp2div x y := fp2mul x (fp2inv y).

(* Works for our prime I guess, cf. https://github.com/zkcrypto/bls12_381/blob/main/src/fp2.rs#L305 *)
Lemma helper1: forall a b, fp_eq (a * a + b * b) fp_zero -> a = fp_zero /\ b = fp_zero.
Proof. Admitted.

Lemma fp2_field_theory: field_theory fp2zero fp2one fp2add fp2mul fp2sub fp2neg fp2div fp2inv fp2eq.
Proof. split.
- apply fp2_ring_theory.
- unfold fp_eq. unfold "<>". intros H. discriminate.
- reflexivity.
- intros p. unfold fp2eq, fp2zero, fp2mul, fp2inv, fp2one, fp2fromfp. destruct p. intros H. apply pair_equal_spec. split; rewrite fp_eq_ok; field;
  intros H1; destruct H; apply helper1 in H1; destruct H1; rewrite H0; rewrite H; apply pair_equal_spec; split; reflexivity.
Qed.

Add Field fp2_field: fp2_field_theory.

Infix "-" := fp2sub.
Infix "+" := fp2add.
Infix "*" := fp2mul.

Definition fp2two := fp2one + fp2one.
Definition fp2three := fp2one + fp2two.


Lemma fp2_same_if_eq: forall x y, fp2_eqb x y = true <-> x = y.
Proof. intros x y. split.
  - unfold fp2_eqb. destruct x. destruct y. intros H. apply Bool.andb_true_iff in H. destruct H. apply fp_same_if_eq in H. apply fp_same_if_eq in H0. rewrite H. rewrite H0. reflexivity.
  - intros H. rewrite H. unfold fp2_eqb. destruct y. repeat rewrite fp_eq_true. reflexivity. 
Qed.

Definition g2_eq (x y: g2) := 
  let '(x1, x2, xinf) := x in
  let '(y1, y2, yinf) := y in
  if xinf then yinf = true else
    x1 = y1 /\ x2 = y2.

(* Fiat-crypto field from standard library field *)
Instance fp2_fc_field : @field fp2 fp2eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul fp2inv fp2div.
Proof.
  repeat split; try apply (Fdiv_def fp_field_theory); try (intros ; field); try apply (_ (fp_field_theory)); auto.
  - symmetry; apply (F_1_neq_0 (fp2_field_theory)).
Qed.


Lemma g2_dec: DecidableRel fp2eq.
Proof. unfold Decidable. unfold fp2eq. intros x y. generalize (fp2_same_if_eq x y). intros H. destruct (fp2_eqb x y).
  - left. apply H. reflexivity. 
  - right. apply not_iff_compat in H. apply H. congruence.
Qed.

About Ring.char_ge.

Lemma fp2_char_ge:  @Ring.char_ge fp2 fp2eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul (BinNat.N.succ_pos BinNat.N.two).
Proof. 
  unfold char_ge. unfold Hierarchy.char_ge. intros pos. simpl. intros H. unfold fp_eq. apply pos_le_three in H. destruct H;
  rewrite H; simpl; intro c; discriminate c.
Qed.

Definition g2_b: fp2 := (fp_four, fp_four).

(* Representation af a Fiat-crypto G1 point *)
Definition g2_fc_point := @W.point fp2 fp2eq fp2add fp2mul fp2zero g2_b. 
(* Fiat-Crypto Equivalence, Addition and Zero element *)
Definition g2_fc_eq := @W.eq fp2 fp2eq fp2add fp2mul fp2zero g2_b.       
Definition g2_fc_add (p1 p2 :g2_fc_point ) :g2_fc_point := @W.add fp2 fp2eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul fp2inv fp2div fp2_fc_field g2_dec fp2_char_ge fp2zero g2_b p1 p2.
Definition g2_fc_zero := @W.zero fp2 fp2eq fp2add fp2mul fp2zero g2_b.

(* ?x? is x performed by hacspec. #x# is x performed by Fiat-Crypto *)
Infix "?+?" := g2add (at level 81).
Infix "?=?" := g2_eq (at level 100).
Infix "#+#" := g2_fc_add (at level 81).
Infix "#=#" := g2_fc_eq (at level 100).

(* Checking the Fiat-Crypto functions actually work*)
Example g2_add_zero_is_zero_in_fc: (g2_fc_zero #+# g2_fc_zero) #=# g2_fc_zero.
Proof. reflexivity.
Qed.

(* Translating Fiat-Crypto Point Representations to our G1 points (x, y, isPointAtInfinity) *)
Definition g2_from_fc (p: g2_fc_point): g2 := 
  match W.coordinates p with
  | inr tt => (fp2zero, fp2zero, true)
  | inl (pair x y) => (x, y, false)
  end.


(* Translating our points to Fiat-Crypto Points *)
Program Definition g2_to_fc (p: g2): g2_fc_point :=
    match p return fp2*fp2+unit with
    | (_, _, true) => inr tt
    | (x, y, false) => if fp2_eqb (y*y) (x*x*x + g2_b) 
      then inl (x, y) 
      else inr tt
    end.
    Opaque fp2mul.
    Next Obligation.
    Crypto.Util.Tactics.BreakMatch.break_match. 
    - trivial. 
    - apply fp2_same_if_eq in Heqb. rewrite Heqb. field. 
    - trivial.
    Qed.

Lemma fp2_eq_ok: forall x y, x = y <-> fp2eq x y.
Proof.
  reflexivity.
Qed.

Lemma fp2_algebra_helper_1: forall x y z, x - y = z <-> x = y + z.
Proof. intros x y z. split.
  - intros H. rewrite <- H. rewrite fp2_eq_ok. field. 
  - intros H. rewrite H. rewrite fp2_eq_ok. field.
Qed.

Lemma fp2_sub_eq_zero_means_same: forall x y, x - y = fp2zero <-> x = y.
Proof. split. 
  - intros H. apply fp2_algebra_helper_1 in H. rewrite H. rewrite fp2_eq_ok. field.
  - intros H. rewrite H. rewrite fp2_eq_ok. field. 
Qed.

(* Integral domain to help with som algebraic properties *)
Definition fp2_integral_domain := @Field.integral_domain fp2 fp2eq fp2zero fp2one fp2neg fp2add fp2mul fp2sub fp2inv fp2div fp2_fc_field g2_dec.

Definition fp2_nonzero_iff := @IntegralDomain.IntegralDomain.nonzero_product_iff_nonzero_factors fp2 fp2eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul fp2_integral_domain.

Lemma fp2_neg_invo: forall x, fp2neg (fp2neg x) = x. 
Proof. intros x.  rewrite fp2_eq_ok. field. 
Qed. 

Lemma fp2_negation_eq_implies_zero: forall x, fp2eq x (fp2neg x) -> x = fp2zero.
Proof. intros x H. unfold fp2eq in H. generalize fp2_field_theory. intros [[]].
  rewrite <- (Radd_0_l (fp2neg x)) in H. rewrite Radd_comm in H.
  rewrite <- fp2_algebra_helper_1 in H.
  rewrite Rsub_def in H.
  rewrite <- fp2_neg_invo.
  assert (x + x = fp2two * x). {  rewrite fp2_eq_ok. unfold fp2two. field. }
  rewrite fp2_neg_invo in H. rewrite H0 in H. generalize (fp2_nonzero_iff fp2two x). intros H1. apply not_iff_compat in H1. destruct H1.
  apply double_negation in H. apply H1 in H. apply Classical_Prop.not_and_or in H. destruct H.
  - destruct H. intros c. discriminate c.
  - apply Classical_Prop.NNPP in H. rewrite H. rewrite fp2_neg_invo. reflexivity.
Qed.

Lemma fp2_square_law: forall x y, x * x - y * y = (x + y) * (x - y).
Proof. intros x y. rewrite fp2_eq_ok. field. 
Qed.

(* Checking if a point is actually on the curve - since FC points are only defined as points on the curve, and our points are everyting from (fp, fp), this is needed *)
Definition g2_on_curve (p:g2) := let '(x, y, inf) := p in if inf then True else y*y=x*x*x + g2_b.

Lemma fp2_symmetrical_x_axis: forall x1 y1 x2 y2, g2_on_curve (x1, y1, false) -> g2_on_curve (x2, y2, false) -> x1 = x2 -> y1 = y2 \/ y1 = fp2neg y2.
Proof. intros x1 y1 x2 y2 H1 H2 H3. generalize (fp2_nonzero_iff (y1 + y2) (y1 - y2)). intro H4.
  unfold g2_on_curve in H1. unfold g2_on_curve in H2. rewrite <- H3 in H2. rewrite <- H2 in H1. apply fp2_sub_eq_zero_means_same in H1. rewrite fp2_square_law in H1.
  apply not_iff_compat in H4. rewrite H1 in H4. unfold fp2eq in H4. destruct H4. 
  (generalize fp2_field_theory). intros [[]]. apply Classical_Prop.not_and_or in H. 
  - destruct H.
    + right. apply fp2_sub_eq_zero_means_same. rewrite Rsub_def. rewrite fp2_neg_invo. apply Classical_Prop.NNPP. apply H.
    + left. apply fp2_sub_eq_zero_means_same. apply Classical_Prop.NNPP. apply H.
  - congruence.
Qed.


Lemma fp2_eq_true: forall x, fp2_eqb x x = true.
Proof. intros x. unfold fp2_eqb. destruct x. repeat rewrite fp_eq_true. reflexivity.
Qed. 

Lemma same_if_g2_eq: forall x y, g2_eqb x y = true -> g2_eq x y.
Proof. intros x y. unfold g2_eqb, g2_eq. destruct x. destruct y. destruct p. destruct p0. intros H.
destruct b.
- destruct (fp2_eqb f f1); destruct (fp2_eqb f0 f2); destruct b0; try reflexivity; try inversion H.
- destruct (fp2_eqb f f1) eqn:E; destruct (fp2_eqb f0 f2) eqn:E1; destruct b0; try reflexivity; try inversion H.
  apply fp2_same_if_eq in E. apply fp2_same_if_eq in E1. split. apply E. apply E1.
Qed.

Lemma fp2from_two: fp2fromfp fp_two = fp2two.
Proof. reflexivity. 
Qed.

Lemma fp2from_three: fp2fromfp fp_three = fp2three.
Proof. reflexivity. 
Qed.

Lemma g2_eqb_true: forall x, g2_eqb x x = true.
Proof.
  intros [[]]. unfold g2_eqb. repeat rewrite fp2_eq_true. rewrite Bool.eqb_reflx. reflexivity.
Qed.


(* The equivalence proof. If two points are on the curve, adding them together using hacspec is the same as converting to fiat-crypto, adding them and converting back *)
Lemma g2_addition_equal: forall p q: g2, g2_on_curve p -> g2_on_curve q -> (p ?+? q) ?=? (g2_from_fc ((g2_to_fc p) #+# (g2_to_fc q))). 
Proof. Opaque g2_eqb. Opaque fp2add. intros p q H H0. unfold g2add. repeat destruct p. destruct q. destruct p. 
  unfold g2_from_fc, g2_to_fc, g2_fc_add. unfold g2_eq. simpl. repeat rewrite fp2from_two. repeat rewrite fp2from_three.
  (generalize fp2_field_theory). intros [[]].
  destruct b eqn:E.
  - destruct b0 eqn:E1.
    + reflexivity.
    + unfold g2_on_curve in H0. rewrite <- H0. rewrite fp2_eq_true. split; reflexivity. 
  - destruct b0 eqn:E1.
    + unfold g2_on_curve in H. rewrite <- H. rewrite fp2_eq_true. split; reflexivity.
    + unfold g2_on_curve in H. unfold g2_on_curve in H0. rewrite H0. rewrite H. repeat rewrite fp2_eq_true.       
    destruct (g2_eqb (f, f0, false) (f1, f2, false)) eqn:E2. 
      * simpl. destruct (fp2_eqb f0 fp2zero) eqn:E3. 
        --  simpl. apply same_if_g2_eq in E2. unfold g2_eq in E2. destruct E2. rewrite H1. unfold fp2eq. unfold dec. destruct (g2_dec f1 f1) eqn:E6. 
          ++ destruct (g2_dec f2 (fp2neg f0)).
            ** reflexivity.
            ** exfalso. rewrite <- H2 in n. apply fp2_same_if_eq in E3. rewrite E3 in n. destruct n. reflexivity.
          ++ exfalso. destruct n. reflexivity.
        -- simpl. apply same_if_g2_eq in E2. simpl in E2. destruct E2. destruct (dec (fp2eq f f1)).
          ++ destruct (dec (fp2eq f2 (fp2neg f0))).
            ** exfalso. rewrite <- H2 in f4. apply fp2_negation_eq_implies_zero in f4. rewrite f4 in E3. rewrite fp2_eq_true in E3. discriminate E3.
            ** split.
              --- rewrite fp2_eq_ok. rewrite H1. unfold fp2three. unfold fp2two. field. split.
                +++ unfold fp2eq. intros c. rewrite c in E3. rewrite fp2_eq_true in E3. discriminate E3.
                +++ unfold fp2eq. intros c. discriminate c.
              --- unfold fp2three. unfold fp2two. rewrite fp2_eq_ok. rewrite H1. field. split. 
                +++ unfold fp2eq. intros c. rewrite c in E3. rewrite fp2_eq_true in E3. discriminate E3.
                +++ unfold fp2eq. intros c. discriminate c.
          ++ rewrite H1 in n. destruct n. reflexivity.
      * destruct (fp2_eqb f f1) eqn:E3.
        -- destruct (fp2_eqb f0 (fp2neg f2)) eqn:E4.
          ++ simpl. destruct (dec (fp2eq f f1)).
            ** destruct (dec (fp2eq f2 (fp2neg f0))).
              --- reflexivity.
              --- exfalso. apply fp2_same_if_eq in E4. rewrite E4 in n. destruct n. field.
            ** exfalso. destruct n. unfold fp2eq. apply (fp2_same_if_eq _ _). apply E3.
          ++ exfalso. generalize (fp2_symmetrical_x_axis f f0 f1 f2 H H0). apply fp2_same_if_eq in E3. intros c. apply c in E3 as H7. destruct H7.
            ** rewrite E3 in E2. rewrite H1 in E2. rewrite g2_eqb_true in E2. discriminate.
            ** rewrite H1 in E4. rewrite fp2_eq_true in E4. discriminate E4.
        -- simpl. destruct (dec (fp2eq f f1)).
          ++ exfalso. unfold fp2eq in f3. rewrite f3 in E3. rewrite fp2_eq_true in E3. discriminate E3.
          ++ split;
            rewrite fp2_eq_ok; field; unfold fp2eq; intros H1; rewrite fp2_sub_eq_zero_means_same in H1; rewrite H1 in E3; rewrite fp2_eq_true in E3; discriminate E3.
Qed.


(* Work in progress. Ignore below. *)

Lemma fc_always_on_curve: forall p: g1_fc_point, g1_on_curve (g1_from_fc p).
Proof. intros p. unfold g1_on_curve, g1_from_fc. unfold W.coordinates. destruct p. destruct x.
- destruct p. unfold fp_eq in y. rewrite y. rewrite fp_eq_ok. field.
- destruct u. trivial.
Qed.

Lemma from_and_back: forall p: g1_fc_point, p = g1_to_fc (g1_from_fc p).
Proof. intros p. unfold g1_to_fc, g1_from_fc. simpl. destruct p. simpl. destruct x.
- destruct p. unfold fp_eqb. assert (f0 * f0 = f * f * f + fp_four).  
  { unfold fp_eq in y. rewrite y. unfold fp_four. rewrite fp_eq_ok. field. }
Admitted.
  

Lemma stuff: forall p q: g1_fc_point, (p #+# q) #=# (g1_to_fc ((g1_from_fc p) ?+? (g1_from_fc q))).
Proof. intros p q. generalize (g1_addition_equal (g1_from_fc p) (g1_from_fc q) (fc_always_on_curve p) (fc_always_on_curve q)). intros H. unfold g1_eq in H.
 destruct (g1_from_fc p ?+? g1_from_fc q) eqn:E. destruct b.
Admitted.