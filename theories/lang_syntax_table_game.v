Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import charge lebesgue_measure numfun lebesgue_integral kernel.
Require Import prob_lang lang_syntax_util lang_syntax lang_syntax_examples.
From mathcomp Require Import ring lra.

(**md**************************************************************************)
(* # Eddy's table game example                                                *)
(*                                                                            *)
(* ref:                                                                       *)
(* - Chung-chieh Shan, Equational reasoning for probabilistic programming,    *)
(*   POPL TutorialFest 2018                                                   *)
(*   https://homes.luddy.indiana.edu/ccshan/rational/equational-handout.pdf   *)
(* - Sean R Eddy, What is Bayesian statistics?, Nature Biotechnology 22(9),   *)
(*   1177--1178 (2004)                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Open Scope ereal_scope.
Lemma letin'_sample_uniform {R : realType} d d' (T : measurableType d)
    (T' : measurableType d') (a b : R) (ab : (a < b)%R)
    (u : R.-sfker [the measurableType _ of (_ * T)%type] ~> T') x y :
  measurable y ->
  letin' (sample_cst (uniform_prob ab)) u x y =
  (b - a)^-1%:E * \int[lebesgue_measure]_(x0 in `[a, b]) u (x0, x) y.
Proof.
move=> my; rewrite letin'E/=.
rewrite integral_uniform//=.
move => _ /= Y mY /=.
have /= := measurable_kernel u _ my measurableT _ mY.
move/measurable_ysection => /(_ R x) /=.
set A := (X in measurable X).
set B := (X in _ -> measurable X).
suff : A = B by move=> ->.
rewrite {}/A {}/B !setTI /ysection/= (*TODO: lemma?*) /preimage/=.
by apply/seteqP; split => [z|z] /=; rewrite inE/=.
Qed.

Local Open Scope lang_scope.
Lemma execP_letin_uniform {R : realType}
  g t str (s0 s1 : exp P ((str, Real) :: g) t) :
  (forall (p : R) x U, (0 <= p <= 1)%R ->
    execP s0 (p, x) U = execP s1 (p, x) U) ->
  forall x U, measurable U ->
  execP [let str := Sample {@exp_uniform _ g 0 1 (@ltr01 R)} in {s0}] x U =
  execP [let str := Sample {@exp_uniform _ g 0 1 (@ltr01 R)} in {s1}] x U.
Proof.
move=> s01 x U mU.
rewrite !execP_letin execP_sample execD_uniform/=.
rewrite !letin'_sample_uniform//.
congr *%E.
apply: eq_integral => p p01.
apply: s01.
by rewrite inE in p01.
Qed.
Local Close Scope lang_scope.
Local Close Scope ereal_scope.

Section bounded.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Local Open Scope ereal_scope.
Context {R : realType}.

Lemma bounded_id_01 : [bounded x0 | x0 in `[0%R, 1%R]%classic : set R].
Proof.
exists 1%R; split => // y y1.
near=> M => /=.
rewrite (le_trans _ (ltW y1))//.
near: M.
move=> M /=.
rewrite in_itv/= => /andP[M0 M1].
by rewrite ler_norml M1 andbT (le_trans _ M0).
Unshelve. all: by end_near. Qed.

Lemma bounded_onem_01 : [bounded (`1- x : R) | x in `[0%R, 1%R]%classic : set R].
Proof.
exists 1%R; split => // y y1.
near=> M => /=.
rewrite (le_trans _ (ltW y1))//.
near: M.
move=> M /=.
rewrite in_itv/= => /andP[M0 M1].
rewrite ler_norml (@le_trans _ _ 0%R)//=.
  by rewrite lerBlDr addrC -lerBlDr subrr.
by rewrite onem_ge0.
Unshelve. all: by end_near. Qed.

Lemma bounded_cst_01 (x : R) : [bounded x | _ in `[0%R, 1%R]%classic : set R].
Proof.
exists `|x|%R; split.
  by rewrite num_real.
move=> y y1/= z.
rewrite in_itv/= => /andP[z0 z1].
by rewrite (le_trans _ (ltW y1)).
Qed.

Lemma bounded_norm (f : R -> R) :
  [bounded f x | x in (`[0%R, 1%R]%classic : set R)] <->
  [bounded normr (f x) | x in (`[0%R, 1%R]%classic : set R)].
Proof.
split.
  move=> [M [Mreal HM]].
  exists `|M|%R; split; first by rewrite normr_real.
  move=> r Mr x/= x01.
  by rewrite ger0_norm// HM// (le_lt_trans _ Mr)// ler_norm.
move=> [M [Mreal HM]].
exists `|M|%R; split; first by rewrite normr_real.
move=> r Mr x/= x01.
rewrite -[leLHS]ger0_norm// HM//.
by rewrite (le_lt_trans _ Mr)// ler_norm.
Qed.

Lemma boundedMl k (f : R -> R) :
  [bounded f x | x in (`[0%R, 1%R]%classic : set R)] ->
  [bounded (k * f x)%R | x in (`[0%R, 1%R]%classic : set R)].
Proof.
move=> [M [Mreal HM]].
exists `|k * M|%R; split; first by rewrite normr_real.
move=> r kMr x/= x01.
rewrite normrM.
have [->|k0] := eqVneq k 0%R.
  by rewrite normr0 mul0r (le_trans _ (ltW kMr)).
rewrite -ler_pdivlMl ?normr_gt0//.
apply: HM => //.
rewrite ltr_pdivlMl ?normr_gt0//.
rewrite (le_lt_trans _ kMr)//.
by rewrite normrM ler_pM2l ?normr_gt0// ler_norm.
Qed.


End bounded.

Lemma measurable_bernoulli_expn {R : realType} U n :
  measurable_fun [set: g_sigma_algebraType R.-ocitv.-measurable]
    (fun x : g_sigma_algebraType (R.-ocitv.-measurable) => bernoulli (`1-x ^+ n) U).
Proof.
apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
by apply: measurable_fun_pow => //=; exact: measurable_funB.
Qed.

Lemma integrable_bernoulli_beta_pdf {R : realType} U : measurable U ->
  (@lebesgue_measure R).-integrable [set: g_sigma_algebraType R.-ocitv.-measurable]
    (fun x => bernoulli (1 - `1-x ^+ 3) U * (beta_pdf 6 4 x)%:E)%E.
Proof.
move=> mU.
have ? : measurable_fun [set: g_sigma_algebraType R.-ocitv.-measurable]
    (fun x => bernoulli (1 - `1-x ^+ 3) U).
  apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
  apply: measurable_funB => //; apply: measurable_fun_pow => //.
  exact: measurable_funB.
apply/integrableP; split => /=.
  apply: emeasurable_funM => //=.
  by apply/EFin_measurable_fun; exact: measurable_beta_pdf.
apply: (@le_lt_trans _ _ (\int[lebesgue_measure]_(x in `[0%R, 1%R]) (beta_pdf 6 4 x)%:E))%E.
  rewrite [leRHS]integral_mkcond /=.
  apply: ge0_le_integral => //=.
  - apply: measurableT_comp => //; apply: emeasurable_funM => //.
    by apply/EFin_measurable_fun; exact: measurable_beta_pdf.
  - move=> x _ /=; rewrite patchE; case: ifPn => // _.
    by rewrite lee_fin beta_pdf_ge0.
  - apply/(measurable_restrict _ _ _) => //.
    apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_beta_pdf.
  - move=> x _.
    rewrite patchE; case: ifPn => x01.
      rewrite gee0_abs//.
        rewrite gee_pMl// ?probability_le1//.
          by rewrite ge0_fin_numE// (le_lt_trans (probability_le1 _ _))// ltry.
        by rewrite lee_fin beta_pdf_ge0.
      by rewrite mule_ge0// lee_fin beta_pdf_ge0.
    by rewrite /beta_pdf /ubeta_pdf patchE (negbTE x01) mul0r mule0 abse0.
apply: (@le_lt_trans _ _
    (\int[lebesgue_measure]_(x in `[0%R, 1%R]) (int_ubeta_pdf 6 4)^-1%:E)%E); last first.
  by rewrite integral_cst//= lebesgue_measure_itv/= lte01 EFinN sube0 mule1 ltry.
apply: ge0_le_integral => //=.
- by move=> ? _; rewrite lee_fin beta_pdf_ge0.
- by apply/measurable_funTS/measurableT_comp => //; exact: measurable_beta_pdf.
- by move=> ? _; rewrite lee_fin invr_ge0// int_ubeta_pdf_ge0.
- by move=> x _; rewrite lee_fin beta_pdf_le_int_ubeta_pdf.
Qed.

Section game_programs.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Definition prog0 : @exp R _ [::] _ :=
 [Normalize
  let "p" := Sample {exp_uniform 0 1 (@ltr01 R)} in
  let "a1" := Sample {exp_binomial 8 [#{"p"}]} in
  let "_" := if #{"a1"} == {5}:N then return TT else Score {0}:R in
  let "a2" := Sample {exp_binomial 3 [#{"p"}]} in
  return {1}:N <= #{"a2"}].

Definition tail1 : @exp R _ [:: ("_", Unit); ("a1", Nat) ; ("p", Real)] _ :=
  [Sample {exp_bernoulli [{1}:R - {[{1}:R - #{"p"}]} ^+ {3%nat}]}].

Definition tail2 : @exp R _ [:: ("_", Unit); ("p", Real)] _ :=
  [Sample {exp_bernoulli [{1}:R - {[{1}:R - #{"p"}]} ^+ {3%nat}]}].

Definition tail3 : @exp R _ [:: ("p", Real); ("_", Unit)] _ :=
  [Sample {exp_bernoulli [{1}:R - {[{1}:R - #{"p"}]} ^+ {3%nat}]}].

Definition prog1 : @exp R _ [::] _ :=
 [Normalize
  let "p" := Sample {exp_uniform 0 1 (@ltr01 R)} in
  let "a1" := Sample {exp_binomial 8 [#{"p"}]} in
  let "_" := if #{"a1"} == {5}:N then return TT else Score {0}:R in
  {tail1}].

Definition prog2 : @exp R _ [::] _ :=
 [Normalize
  let "p" := Sample {exp_uniform 0 1 (@ltr01 R)} in
  let "_" :=
    Score {[{56}:R * #{"p"} ^+ {5%nat} * {[{1}:R - #{"p"}]} ^+ {3%nat}]} in
  {tail2}].

Definition prog2' : @exp R _ [::] _ :=
 [Normalize
  let "p" := Sample {exp_beta 1 1} in
  let "_" := Score
    {[{56}:R * #{"p"} ^+ {5%nat} * {[{1}:R - #{"p"}]} ^+ {3%N}]} in
  {tail2}].

Definition prog3 : @exp R _ [::] _ :=
 [Normalize
  let "_" := Score {1 / 9}:R in
  let "p" := Sample {exp_beta 6 4} in
  {tail3}].

Definition prog4 : @exp R _ [::] _ :=
 [Normalize
  let "_" := Score {1 / 9}:R in
  Sample {exp_bernoulli [{10 / 11}:R]}].

Definition prog5 : @exp R _ [::] _ :=
  [Normalize Sample {exp_bernoulli [{10 / 11}:R]}].

End game_programs.
Arguments tail1 {R}.
Arguments tail2 {R}.

Section from_prog0_to_prog1.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Let prog01_subproof
  (x : mctx (untag (ctx_of (recurse Unit (recurse Nat (found "p" Real [::])))))) U :
  (0 <= x.2.2.1 <= 1)%R ->
  execP [let "a2" := Sample {exp_binomial 3 [#{"p"}]} in
         return {1}:N <= #{"a2"}] x U =
  execP (@tail1 R) x U.
Proof.
move=> x01.
rewrite /tail1.
(* reduce lhs *)
rewrite execP_letin execP_sample execD_binomial/= execP_return/= execD_rel/=.
rewrite exp_var'E (execD_var_erefl "p")/=.
rewrite exp_var'E (execD_var_erefl "a2")/=.
rewrite execD_nat/=.
rewrite [LHS]letin'E/=.
(* reduce rhs *)
rewrite execP_sample/= execD_bernoulli/= (@execD_bin _ _ binop_minus)/=.
rewrite execD_real/= execD_pow/= (@execD_bin _ _ binop_minus)/= execD_real/=.
rewrite (execD_var_erefl "p")/=.
exact/integral_binomial_prob.
Qed.

Lemma prog01 : execD (@prog0 R) = execD (@prog1 R).
Proof.
rewrite /prog0 /prog1.
apply: congr_normalize => y A.
apply: execP_letin_uniform => // p [] B p01.
apply: congr_letinr => a1 V0.
apply: congr_letinr => -[] V1.
exact: prog01_subproof.
Qed.

End from_prog0_to_prog1.

Section from_prog1_to_prog2.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Let prog12_subproof (y : @mctx R [::]) (V : set (@mtyp R Bool))
  (p : R)
  (x : projT2 (existT measurableType default_measure_display unit))
  (U : set (mtyp Bool))
  (p0 : (0 <= p)%R)
  (p1 : (p <= 1)%R) :
  \int[binomial_prob 8 p]_y0
     execP [let "_" := if #{"a1"} == {5} :N then return TT else Score {0}:R in {tail1}]
       (y0, (p, x)) U =
  \int[mscale (NngNum (normr_ge0 (56 * XnMonemXn 5 3 p))) \d_tt]_y0
     execP tail2 (y0, (p, x)) U.
Proof.
rewrite integral_binomial//=.
rewrite (bigD1 (inord 5))//=.
rewrite big1 ?adde0; last first.
  move=> i i5.
  rewrite execP_letin/= execP_if/= execD_rel/=.
  rewrite exp_var'E/= (execD_var_erefl "a1")/=.
  rewrite execD_nat/= execP_score/= execD_real/= execP_return/=.
  rewrite letin'E iteE/=.
  move: i => [[|[|[|[|[|[|[|[|[|//]]]]]]]]]]//= Hi in i5 *;
  rewrite ?ge0_integral_mscale//= ?execD_real/= ?normr0 ?(mul0e,mule0)//.
  by rewrite -val_eqE/= inordK in i5.
(* reduce lhs *)
rewrite -[(p ^+ _ * _ ^+ _)%R]/(XnMonemXn _ _ p).
rewrite execP_letin/= execP_if/= execD_rel/=.
rewrite exp_var'E/= (execD_var_erefl "a1")/=.
rewrite execD_nat/= execP_score/= execD_real/= execP_return/=.
rewrite letin'E iteE/=.
rewrite inordK// eqxx.
rewrite integral_dirac//= execD_unit/= diracE mem_set// mul1e.
(* reduce rhs *)
rewrite ge0_integral_mscale//=.
rewrite integral_dirac//= diracE mem_set// mul1e.
rewrite ger0_norm ?mulr_ge0 ?subr_ge0//.
rewrite mulr_natl.
(* same score *)
congr *%E.
(* the tails are the same module the shape of the environment *)
rewrite /tail1 /tail2 !execP_sample/=.
rewrite !execD_bernoulli/=.
rewrite !(@execD_bin _ _ binop_minus)/=.
rewrite !execD_pow/=.
rewrite !execD_real/=.
rewrite !(@execD_bin _ _ binop_minus)/=.
by rewrite !execD_real/= !exp_var'E/= !(execD_var_erefl "p")/=.
Qed.

Lemma prog12 : execD (@prog1 R) = execD (@prog2 R).
Proof.
apply: congr_normalize => y V.
apply: execP_letin_uniform => // p x U /andP[p0 p1].
(* reduce the lhs *)
rewrite execP_letin execP_sample execD_binomial/=.
rewrite letin'E/=.
rewrite [in LHS]exp_var'E/= (execD_var_erefl "p")/=.
(* reduce the rhs *)
rewrite [in RHS]execP_letin execP_score/=.
rewrite letin'E/=.
do 2 rewrite (@execD_bin _ _ binop_mult)/=/=.
rewrite [in RHS]exp_var'E/=.
rewrite execD_pow/=.
rewrite (execD_var_erefl "p")/=.
rewrite execD_pow/=.
rewrite (@execD_bin _ _ binop_minus)/=/=.
rewrite 2!execD_real/=.
rewrite (execD_var_erefl "p")/=.
rewrite -(mulrA 56).
exact: prog12_subproof.
Qed.

End from_prog1_to_prog2.

Section from_prog2_to_prog3.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Lemma prog22' : execD (@prog2 R) = execD (@prog2' R).
Proof.
apply: congr_normalize => // x U.
apply: congr_letinl => // y V.
rewrite !execP_sample execD_uniform/= execD_beta/=.
by rewrite Beta_uniform.
Qed.

Let measurable_bernoulli_onemXn U :
  measurable_fun [set: g_sigma_algebraType R.-ocitv.-measurable]
    (fun x => bernoulli (1 - `1-x ^+ 3) U).
Proof.
apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
apply: measurable_funB => //.
by apply: measurable_fun_pow; exact: measurable_funB.
Qed.

Let bounded_norm_XnonemXn :
  [bounded normr (56 * XnMonemXn 5 3 x)%R : R | x in `[0%R, 1%R] : set R].
Proof. exact/(bounded_norm _).1/boundedMl/bounded_XnMonemXn. Qed.

Let integrable_bernoulli_XnMonemXn U : (Beta 1 1).-integrable [set: R]
  (fun x => bernoulli (1 - `1-x ^+ 3) U * (normr (56 * XnMonemXn 5 3 x))%:E).
Proof.
apply/integrableP; split.
  apply: emeasurable_funM => //; apply/EFin_measurable_fun => //.
  apply: measurableT_comp => //; apply: measurable_funM => //.
  exact: measurable_fun_XnMonemXn.
rewrite Beta_uniform integral_uniform//=.
  rewrite subr0 invr1 mul1e.
  suff : mu.-integrable `[0%R, 1%R]
    (fun y : R => bernoulli (1 - `1-y ^+ 3) U * (normr (56 * XnMonemXn 5 3 y))%:E).
    by move=> /integrableP[].
  apply: integrableMl => //=.
  - apply/integrableP; split; first exact: measurable_funTS.
    have := @integral_Beta_bernoulli_onem_lty R 3 1%N 1%N U.
    rewrite Beta_uniform integral_uniform//=; last exact: measurableT_comp.
    by rewrite subr0 invr1 mul1e.
  - apply: @measurableT_comp => //=; apply: measurable_funM => //.
    exact: measurable_fun_XnMonemXn.
apply: @measurableT_comp => //; apply: emeasurable_funM => //=.
do 2 apply: @measurableT_comp => //=.
by apply: measurable_funM => //; exact: measurable_fun_XnMonemXn.
Qed.

Lemma prog23 : execD (@prog2' R) = execD (@prog3 R).
Proof.
apply: congr_normalize => x U.
rewrite !execP_letin !execP_sample !execP_score !execD_beta.
rewrite !execD_bernoulli/= !(@execD_bin _ _ binop_mult).
do 2 (rewrite !execD_pow !(@execD_bin _ _ binop_minus) !execD_real/=).
rewrite !exp_var'E !(execD_var_erefl "p")/=.
rewrite [LHS]letin'E/=.
under eq_integral => y _.
  rewrite letin'E/=.
  rewrite integral_cst//= /mscale/= diracT mule1 -mulrA -/(XnMonemXn _ _ _).
  over.
rewrite [RHS]letin'E/=.
under [in RHS]eq_integral => y _.
  rewrite letin'E/=.
  over.
rewrite /=.
rewrite [RHS]ge0_integral_mscale//=; last first.
  by move=> _ _; rewrite integral_ge0.
rewrite integral_Beta//=; last 2 first.
  - apply: emeasurable_funM => //=; apply/EFin_measurable_fun.
    apply: measurableT_comp => //; apply: measurable_funM => //.
    exact: measurable_fun_XnMonemXn.
  - by have /integrableP[] := integrable_bernoulli_XnMonemXn U.
rewrite ger0_norm// integral_dirac// diracT mul1e.
rewrite integral_Beta/=; [|by []|by []|exact: integral_Beta_bernoulli_onem_lty].
rewrite -integralZl//=; last exact: integrable_bernoulli_beta_pdf.
apply: eq_integral => y _.
rewrite /beta_pdf /ubeta_pdf.
rewrite !patchE; case: ifPn => [y01|]; last first.
  by rewrite !(mul0r,mulr0,mule0).
rewrite [RHS]muleCA -!muleA.
congr *%E.
rewrite /= XnMonemXn00 int_ubeta_pdf11 divr1 mule1.
rewrite normrM [X in (_ * X)%R]ger0_norm//; last first.
  by rewrite XnMonemXn_ge0; rewrite inE in y01.
rewrite ger0_norm// -!EFinM; congr EFin.
by rewrite !int_ubeta_pdfE/= factE/= /onem; lra.
Qed.

End from_prog2_to_prog3.

Module prog34test.
Section prog34test.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.


Lemma int_Beta01 U :
  \int[Beta 6 4]_y bernoulli ((1 - y) ^+ 3) U =
  \int[Beta 6 4]_(y in `[0%R, 1%R] : set R) bernoulli (`1-y ^+ 3) U.
Proof.
rewrite [LHS]integral_Beta//=; last 2 first.
  by apply: measurable_funTS; apply: measurable_bernoulli_expn.
  apply: (le_lt_trans _ (integral_Beta_bernoulli_onemXn_lty 3 6 4 U)).
  apply: ge0_subset_integral => //=; apply: measurableT_comp => //=.
  apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
  by apply: measurable_fun_pow => //=; exact: measurable_funB.
rewrite [RHS]integral_Beta//; last 2 first.
  apply/measurable_funTS.
  exact: measurable_bernoulli_expn.
  apply: (le_lt_trans _ (integral_Beta_bernoulli_onemXn_lty 3 6 4 U)).
  apply: ge0_subset_integral => //=; apply: measurableT_comp => //=.
  apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
  by apply: measurable_fun_pow => //=; exact: measurable_funB.
rewrite [RHS]integral_mkcond/=; apply: eq_integral => x _ /=.
rewrite !patchE; case: ifPn => // x01.
by rewrite /beta_pdf /ubeta_pdf patchE (negbTE x01) mul0r mule0.
Qed.

Lemma int_Beta_bernoulli (U : set (@mtyp R Bool)) :
 \int[Beta 6 4]_y bernoulli ((1 - y) ^+ 3) U = bernoulli (1 / 11) U :> \bar R.
Proof.
rewrite int_Beta01.
have := @Beta_bernoulliE R 6 4 0 3 U isT isT.
rewrite /Beta_bernoulli /ubeta_pdf /=.
under eq_integral.
  move=> x x0.
  rewrite patchE x0 XnMonemXn0.
  over.
rewrite /= => ->; congr bernoulli.
by rewrite /div_beta_norm addn0 !int_ubeta_pdfE/= !factE/=; field.
Qed.

Lemma prog34' U :
  @execP R [::] _ [let "p" := Sample {exp_beta 6 4} in
         Sample {exp_bernoulli [{[{1}:R - #{"p"}]} ^+ {3%N}]}] tt U =
  @execP R [::] _ [Sample {exp_bernoulli [{1 / 11}:R]}] tt U.
Proof.
(* reduce the lhs *)
rewrite execP_letin.
rewrite execP_sample execD_beta/=.
rewrite execP_sample/= execD_bernoulli/=.
rewrite execD_pow/= (@execD_bin _ _ binop_minus) execD_real/=.
rewrite exp_var'E (execD_var_erefl "p")/=.
(* reduce the rhs *)
rewrite execP_sample execD_bernoulli/= execD_real.
(* semantics of lhs *)
rewrite letin'E/=.
exact: int_Beta_bernoulli.
Qed.

End prog34test.
End prog34test.

Section from_prog3_to_prog4.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Lemma integral_bernoulli_beta_pdf' (f : _ -> R) U (g : R -> R) :
  measurable_fun setT f ->
  (forall x, x \in (`[0%R, 1%R]%classic : set R) -> 0 <= f x <= 1)%R ->
  (forall x, 0 <= g x)%R ->
  measurable_fun setT g ->
  \int[mu]_(x in `[0%R, 1%R]) (g x)%:E = 1 ->
  (mu.-integrable `[0%R, 1%R] (EFin \o (f \* g)%R)) ->
  \int[mu]_(y in `[0%R, 1%R]) (bernoulli (1 - f y) U * (g y)%:E) =
  (\d_true U + \d_false U) - \int[mu]_(y in `[0%R, 1%R]) (bernoulli (f y) U * (g y)%:E).
Proof.
move=> mf f01 g0 mg ig1 fg.
have ? : mu.-integrable `[0%R, 1%R] (EFin \o g).
  apply/integrableP; split => //.
    apply/measurable_funTS.
    exact/EFin_measurable_fun.
  under eq_integral.
    move=> x _.
    rewrite /= ger0_norm//.
    over.
  rewrite /=.
  by rewrite ig1 ltry.
have f0 x : x \in (`[0%R, 1%R]%classic : set R) -> (0 <= f x)%R.
  by move => /f01/andP[].
have f1 x : x \in (`[0%R, 1%R]%classic : set R) -> (f x <= 1)%R.
  by move => /f01/andP[].
under eq_integral => x.
  move=> x01.
  rewrite bernoulliE//=; last first.
    by rewrite subr_ge0 f1//= lerBlDr addrC -lerBlDr subrr f0.
  over.
rewrite /=.
under [LHS]eq_integral.
  rewrite /= => x _.
  rewrite onemK muleDl//.
  over.
rewrite /=.
rewrite ge0_integralD//=; last 4 first.
  move=> x x01; rewrite mule_ge0// ?lee_fin ?beta_pdf_ge0//.
  by rewrite mulr_ge0// subr_ge0// f1// inE.
  apply: measurable_funTS; apply: emeasurable_funM => //.
    by apply: emeasurable_funM => //; exact/EFin_measurable_fun/measurable_funB.
  by apply/EFin_measurable_fun; exact: mg.
  by move=> x x01; rewrite mule_ge0// ?lee_fin ?beta_pdf_ge0// mulr_ge0// f0// inE.
  apply: measurable_funTS; apply: emeasurable_funM => //.
    by apply: emeasurable_funM; exact/EFin_measurable_fun.
  by apply/EFin_measurable_fun; exact: mg.
under eq_integral do rewrite muleAC/=.
rewrite ge0_integralZr//=; last 2 first.
  apply: measurable_funTS; apply: emeasurable_funM => //.
    by apply/EFin_measurable_fun/measurable_funB.
  by apply/EFin_measurable_fun; exact: mg.
  move=> x x01.
  by rewrite mule_ge0// lee_fin// ?subr_ge0// ?f1// ?inE// beta_pdf_ge0.
under [X in _ + X = _]eq_integral do rewrite muleAC/=.
rewrite [X in _ + X = _]ge0_integralZr//=; last 2 first.
  apply: measurable_funTS; apply: emeasurable_funM => //.
    exact/EFin_measurable_fun.
  by apply/EFin_measurable_fun; exact: mg.
  by move=> x x01; rewrite mule_ge0// lee_fin// ?f0// ?inE// beta_pdf_ge0.
under [in RHS]eq_integral => x x01.
  rewrite bernoulliE//=; last by rewrite f0//= f1.
  rewrite muleDl//.
  over.
rewrite /= ge0_integralD//=; last 4 first.
  move=> x x01; rewrite mule_ge0// ?lee_fin ?beta_pdf_ge0// mulr_ge0// f0//.
  by rewrite inE.
  apply: measurable_funTS; apply: emeasurable_funM => //.
    by apply: emeasurable_funM => //; apply/EFin_measurable_fun.
  by apply/EFin_measurable_fun; exact: mg.
  move=> x x01; rewrite mule_ge0// ?lee_fin ?beta_pdf_ge0// mulr_ge0//.
  by rewrite subr_ge0 f1// inE.
  apply: measurable_funTS;apply: emeasurable_funM => //.
    by apply: emeasurable_funM => //; apply/EFin_measurable_fun/measurable_funB.
  by apply/EFin_measurable_fun; exact: mg.
under [X in _ = _ - (X + _)]eq_integral do rewrite muleAC/=.
rewrite [X in _ = _ - (X + _)]ge0_integralZr//=; last 2 first.
  apply: measurable_funTS => //; apply: emeasurable_funM => //.
    by apply/EFin_measurable_fun.
  by apply/EFin_measurable_fun; exact: mg.
  by move=> x x01; rewrite mule_ge0// lee_fin// ?f0// ?inE// beta_pdf_ge0.
under [X in _ = _ - (_ + X)]eq_integral do rewrite muleAC/=.
rewrite [X in _ = _ - (_ + X)]ge0_integralZr//=; last 2 first.
  apply: measurable_funTS => //; apply: emeasurable_funM => //.
    by apply/EFin_measurable_fun/measurable_funB.
  by apply/EFin_measurable_fun; exact: mg.
  move=> x x01; rewrite mule_ge0// lee_fin// ?beta_pdf_ge0//.
  by rewrite subr_ge0 f1// inE.
rewrite oppeD//; last first.
  rewrite ge0_adde_def// inE mule_ge0// integral_ge0//= => x x01;
  by rewrite mule_ge0 ?lee_fin ?beta_pdf_ge0// ?subr_ge0 ?f0 ?f1 ?inE.
rewrite addrA.
rewrite -mulNe.
 rewrite -integral_ge0N//=; last first.
  by move=> x x01; rewrite mule_ge0 ?lee_fin ?beta_pdf_ge0// f0// inE.
rewrite -mulNe.
rewrite -integral_ge0N//=; last first.
  by move=> x x01; rewrite mule_ge0 ?lee_fin ?beta_pdf_ge0// subr_ge0 f1// inE.
under [X in _ = (_ + _ + X * _)%E]eq_integral.
  move=> /= y _.
  rewrite /onem mulrBl mul1r opprB EFinB.
  over.
rewrite /=.
rewrite -addeA.
rewrite addeACA.
rewrite -[in X in _ = _ + (X + _)](mul1e (\d_false U)).
rewrite -muleDl//.
rewrite -[in X in _ = X + _ + _](mul1e (\d_true U)).
rewrite -muleDl//.
congr (_ * _ + _ * _).
  under eq_integral do rewrite EFinB muleBl// mul1e.
  rewrite integralB_EFin//=.
  under [in RHS]eq_integral do rewrite EFinN EFinM.
  rewrite [X in _ = _ + X]integral_ge0N //; last first.
    move=> x x01.
    by rewrite mule_ge0// lee_fin// ?f0 ?inE// beta_pdf_ge0.
  rewrite /=.
  congr (_ - _).
  by rewrite ig1.
rewrite integralB_EFin//=.
rewrite addeCA.
by rewrite ig1 subee ?adde0//.
Qed.

Lemma integral_bernoulli_beta_pdf (f : _ -> R) U p m n :
  measurable_fun setT f ->
  (forall x, x \in (`[0%R, 1%R]%classic : set R) -> 0 <= f x <= 1)%R ->
  (\int[mu]_(y in `[0%R, 1%R]) (bernoulli (f y) U * (beta_pdf m n y)%:E) = p%:E * \d_true U + (1 - p%:E) * \d_false U)%E ->
  (\int[mu]_(y in `[0%R, 1%R]) (bernoulli (1 - f y) U * (beta_pdf m n y)%:E) = (1 - p%:E) * \d_true U + p%:E * \d_false U)%E.
Proof.
move=> mf f01 H /=.
rewrite integral_bernoulli_beta_pdf'//=; last 4 first.
  move=> x.
  by rewrite beta_pdf_ge0.
  exact: measurable_beta_pdf.
  by rewrite integral_beta_pdf// Beta01.
  apply/integrableP; split.
    apply/EFin_measurable_fun; apply/measurable_funM => //.
      exact: measurable_funTS.
    apply: measurable_funTS.
    exact: measurable_beta_pdf.
    rewrite /=.
    apply: (@le_lt_trans _ _ (\int[mu]_(x in `[0%R, 1%R]) (int_ubeta_pdf m n)^-1%:E)).
      apply: ge0_le_integral => //=.
        do 2 apply: measurableT_comp => //=.
        by apply: measurable_funM => //=; apply/measurable_funTS => //; exact: measurable_beta_pdf.
      by move=> _ _; rewrite lee_fin invr_ge0// int_ubeta_pdf_ge0.
    move=> x x01.
    rewrite ger0_norm//; last first.
      rewrite mulr_ge0// ?beta_pdf_ge0//.
      rewrite -inE in x01.
      by have /andP[] := f01 _ x01.
    rewrite /beta_pdf.
    rewrite lee_fin.
    rewrite -[leRHS]mul1r.
    rewrite ler_pM// ?beta_pdf_ge0//.
      rewrite -inE in x01.
      by have /andP[] := f01 _ x01.
      rewrite -inE in x01.
      by have /andP[] := f01 _ x01.
    exact: beta_pdf_le_int_ubeta_pdf.
    by rewrite integral_cst//= lebesgue_measure_itv//= lte01 EFinN sube0 mule1 ltry.
rewrite H.
rewrite oppeD//.
rewrite addeACA.
rewrite -{1}(mul1e (\d_true U)).
rewrite -{1}(mul1e (\d_false U)).
rewrite -muleBl//.
rewrite -muleBl//.
by rewrite EFinN oppeB// addrA subee// add0e.
Qed.

Lemma int_Beta_bernoulli_onem (U : set (@mtyp R Bool)) :
  \int[Beta 6 4]_y0 bernoulli (1 - (1 - y0) ^+ 3) U = bernoulli (10 / 11) U :> \bar R.
Proof.
rewrite bernoulliE//=; last lra.
rewrite integral_Beta//; last first.
  by have := @integral_Beta_bernoulli_onem_lty R _ _ _ U.
  apply: (measurableT_comp (measurable_bernoulli2 _)) => //.
  apply: measurable_funB => //; apply: measurable_fun_pow => //.
  exact: measurable_funB.
transitivity (\int[mu]_(x in `[0%R, 1%R])
    (bernoulli (1 - `1-x ^+ 3) U * (beta_pdf 6 4 x)%:E) : \bar R)%E.
  rewrite [RHS]integral_mkcond; apply: eq_integral => z _.
  rewrite /= !patchE; case: ifPn => // z01.
  by rewrite /beta_pdf /ubeta_pdf patchE (negbTE z01) mul0r mule0.
rewrite (@integral_bernoulli_beta_pdf (fun x => `1-x ^+ 3)%R U (1 / 11))//=; last 3 first.
  by apply: measurable_fun_pow => //; exact: measurable_funB.
  move=> z.
  rewrite inE/= in_itv/= => /andP[z0 z1].
  rewrite exprn_ge0 ?subr_ge0//= exprn_ile1// ?subr_ge0//.
  by rewrite lerBlDr addrC -lerBlDr subrr.
  transitivity (Beta_bernoulli 6 4 0 3 U : \bar R).
    rewrite /Beta_bernoulli /ubeta_pdf/= /onem.
    rewrite [RHS]integral_Beta//; last 2 first.
      apply: (measurableT_comp (measurable_bernoulli2 _)) => //.
      apply/(measurable_restrict _ _ _).1 => //=.
      exact: measurable_fun_XnMonemXn.
    rewrite (le_lt_trans _ (integral_Beta_bernoulli_onemXn_lty 3 6 4 U))//.
    rewrite integral_mkcond /=; apply: ge0_le_integral => //=.
      by move=> z _; rewrite patchE; case: ifPn.
      apply/(measurable_restrict _ _ _) => //; apply: measurableT_comp => //=.
      apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
      apply/(measurable_restrict _ _ _).1 => //=; rewrite ?setTI//.
      exact: measurable_fun_XnMonemXn.
      by apply/measurableT_comp => //; exact: measurable_bernoulli_expn.
      move=> z _; rewrite !patchE; case: ifPn => z01.
        by rewrite z01 XnMonemXn0.
      exact: abse_ge0.
    apply: eq_integral => z z01.
    by rewrite patchE z01 XnMonemXn0.
  rewrite Beta_bernoulliE//= bernoulliE//=; last first.
    by rewrite div_beta_norm_ge0// div_beta_norm_le1.
  by congr (_ * _ + _ * _)%:E; rewrite /onem;
    rewrite /div_beta_norm !int_ubeta_pdfE/= !factE/=; field.
congr (_ * _ + _ * _)%E.
  by rewrite -EFinD; congr EFin; lra.
by congr _%:E; rewrite /onem; lra.
Qed.

Lemma prog34 : execD (@prog3 R) = execD (@prog4 R).
Proof.
apply: congr_normalize => y V.
apply: congr_letinr => x U.
rewrite execP_letin !execP_sample execD_beta !execD_bernoulli/=.
rewrite (@execD_bin _ _ binop_minus) execD_pow/= (@execD_bin _ _ binop_minus).
rewrite !execD_real/= exp_var'E (execD_var_erefl "p")/=.
rewrite letin'E/=.
exact: int_Beta_bernoulli_onem.
Qed.

End from_prog3_to_prog4.

Section from_prog4_to_prog5.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Lemma normalize_score_bernoulli g p q (p0 : (0 < p)%R) (q01 : (0 <= q <= 1)%R) :
  @execD R g _ [Normalize let "_" := Score {p}:R in
                Sample {exp_bernoulli [{q}:R]}] =
  execD [Normalize Sample {exp_bernoulli [{q}:R]}].
Proof.
apply: eq_execD.
rewrite !execD_normalize_pt/= !execP_letin !execP_score.
rewrite !execP_sample !execD_bernoulli !execD_real/=.
apply: funext=> x.
apply: eq_probability=> /= y.
rewrite !normalizeE/=.
rewrite !bernoulliE//=; [|lra..].
rewrite !diracT !mule1 -EFinD add_onemK onee_eq0/=.
rewrite !letin'E.
under eq_integral.
  move=> x0 _ /=.
  rewrite !bernoulliE//=; [|lra..].
  rewrite !diracT !mule1 -EFinD add_onemK.
  over.
rewrite !ge0_integral_mscale//= (ger0_norm (ltW p0))//.
rewrite integral_dirac// !diracT !indicT /= !mule1.
rewrite gt_eqF ?lte_fin//=.
rewrite integral_dirac//= diracT !mul1e !mulr1.
rewrite addrCA subrr addr0 invr1 mule1.
rewrite !bernoulliE//=; [|lra..].
by rewrite muleAC -EFinM divff// ?gt_eqF// mul1r EFinD.
Qed.

Lemma prog45 : execD (@prog4 R) = execD (@prog5 R).
Proof. by rewrite normalize_score_bernoulli//; lra. Qed.

End from_prog4_to_prog5.

Lemma from_prog0_to_prog5 {R : realType} :
  projT1 (execD (@prog0 R)) tt = projT1 (execD (@prog5 R)) tt.
Proof.
by rewrite prog01 prog12 prog22' prog23 prog34 prog45.
Qed.
