From Coq Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp.classical Require Import mathcomp_extra boolp.
From mathcomp Require Import ring lra.
From mathcomp Require Import classical_sets functions cardinality fsbigop.
From mathcomp Require Import signed reals ereal topology normedtype sequences.
From mathcomp Require Import esum measure lebesgue_measure numfun exp trigo.
From mathcomp Require Import realfun lebesgue_integral kernel kernel.
From mathcomp Require Import probability prob_lang.
From mathcomp Require Import lang_syntax_util lang_syntax lang_syntax_examples.

(**md**************************************************************************)
(* # Inferring behavior from text-massage data example                        *)
(*                                                                            *)
(* ref:                                                                       *)
(* - Chung-chieh Shan, Equational reasoning for probabilistic programming,    *)
(*   POPL TutorialFest 2018                                                   *)
(*   https://homes.luddy.indiana.edu/ccshan/rational/equational-handout.pdf   *)
(* - *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.ExtraDef Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section hello_programs.
Local Open Scope lang_scope.
Context {R : realType}.
Local Notation mu := lebesgue_measure.

Definition guard_real {g} str (r : R) :
 @exp R P [:: (str, _) ; g] _ :=
  [if #{str} ==R {r}:R then return TT else Score {0}:R].

Definition helloWrong (y0 : R) : @exp R _ [::] _ :=
 [Normalize
  let "x" := Sample {exp_normal ltr01 (exp_real 0)} in
  let "y" := Sample {exp_normal ltr01 [#{"x"}]} in
  let "_" := {guard_real "y" y0} in
  let "z" := Sample {exp_normal ltr01 [#{"x"}]} in
  return #{"z"}].

Definition helloRight : @exp R _ [:: ("y0", Real)] _ :=
 [Normalize
  let "x" := Sample {exp_normal ltr01 (exp_real 0)} in
  let "_" := Score {expR 1} `^
                     ({0}:R - (#{"y0"} - #{"x"}) ^+ {2} * {2^-1}:R)
                   * {(Num.sqrt 2 * pi)^-1}:R in
 return #{"x"}].

Definition helloJoint : @exp R _ [::] _ :=
 [Normalize
  let "x" := Sample {exp_normal ltr01 (exp_real 0)} in
  let "y" := Sample {exp_normal ltr01 [#{"x"}]} in
  let "z" := Sample {exp_normal ltr01 [#{"x"}]} in
 return (#{"y"}, #{"z"})].

End hello_programs.

Section helloRight_proof.
Local Open Scope lang_scope.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Variable y0 : R.

Let ltr0Vsqrt2 : (0 < (@Num.sqrt R 2)^-1)%R.
Proof. by []. Qed.

Let ltr03Vsqrt2 : (0 < 3 * (@Num.sqrt R 2)^-1)%R.
Proof. by []. Qed.

Definition helloRight1 : @exp R _ [:: ("y0", Real)] _ :=
 [Normalize
  let "_" := Score {expR 1} `^ ({0}:R - #{"y0"} ^+ {2} * {4^-1}:R) *
                   {(Num.sqrt (4 * pi))^-1}:R in
  let "x" := Sample {exp_normal ltr0Vsqrt2 [#{"y0"} * {2^-1}:R ]} in
  let "z" := Sample {exp_normal ltr01 [#{"x"}]} in
 return #{"z"}].

Definition helloRight2 : @exp R _ [:: ("y0", Real)] _ :=
 [Normalize
  let "_" := Score {expR 1} `^ ({0}:R - #{"y0"} ^+ {2} * {4^-1}:R) *
                   {(Num.sqrt (4 * pi))^-1}:R in
  Sample {exp_normal ltr03Vsqrt2 [#{"y0"} * {2^-1}:R]}].

Local Import gaussian.
(*Local Notation "normal_prob m s s0" := (normal_prob m s s0 interal_normal). *)
(* TODO: prove *)
Axiom integral_normal_prob : forall (m s : R) (s0 : (0 < s)%R) f U,
  measurable U ->
  measurable_fun U f ->
  \int[@normal_prob _ m s s0 (integral_normal m s0)]_(x in U) `|f x| < +oo ->
  \int[@normal_prob _ m s s0 (integral_normal m s0)]_(x in U) f x =
  \int[mu]_(x in U) (f x * (normal_pdf m s x)%:E).

Lemma helloRight12' u U :
 @execP R [:: ("y0", Real)] _
   [let "x" := Sample {exp_normal ltr0Vsqrt2 [#{"y0"} * {2^-1}:R ]} in
    let "z" := Sample {exp_normal ltr01 [#{"x"}]} in
    return #{"z"}] u U =
 @execP R [:: ("y0", Real)] _
   [Sample {exp_normal ltr03Vsqrt2 [#{"y0"} * {2^-1}:R]}] u U.
Proof.
rewrite !execP_letin.
rewrite !execP_sample !execD_normal/=.
rewrite (@execD_bin _ _ binop_mult) execD_real/=.
rewrite execP_return.
rewrite !exp_var'E (execD_var_erefl "y0") (execD_var_erefl "x") (execD_var_erefl "z")/=.
rewrite !letin'E/=.
(* rhs *)
rewrite [RHS]/normal_prob.
rewrite integral_normal_prob//=; first last.
- admit.
- admit.
rewrite [RHS]integral_mkcond/=.
apply: eq_integral => x _.
rewrite letin'E/=.
rewrite integral_normal_prob//=; first last.
- admit.
- admit.
(* Radon_Nikodym *)
Admitted.

Lemma helloRight1_to_2 : execD helloRight1 = execD helloRight2.
Proof.
apply: eq_execD.
rewrite /helloRight1/helloRight2.
rewrite !execD_normalize_pt/=.
rewrite !execP_letin.
rewrite !execP_score.
rewrite !execD_pow_real/=.
rewrite !execP_sample.
rewrite execP_return/=.
Abort.

End helloRight_proof.

(* TODO: move *)
Section exponential_pdf.
Context {R : realType}.
Notation mu := lebesgue_measure.
Variable (mean : R).
Hypothesis mean0 : (0 < mean)%R.

Definition exponential_pdf' (x : R) := (mean^-1 * expR (- x / mean))%R.
Definition exponential_pdf := exponential_pdf' \_ `[0%R, +oo[.

Lemma exponential_pdf_ge0 (x : R) : (0 <= exponential_pdf x)%R.
Proof.
apply: restrict_ge0 => {}x _.
apply: mulr_ge0; last exact: expR_ge0.
by rewrite invr_ge0 ltW.
Qed.

End exponential_pdf.

Definition exponential {R : realType} (m : R)
  of \int[@lebesgue_measure R]_x (exponential_pdf m x)%:E = 1%E : set _ -> \bar R :=
  fun V => (\int[lebesgue_measure]_(x in V) (exponential_pdf m x)%:E)%E.

Section exponential.
Context {R : realType}.
Local Open Scope ring_scope.

Notation mu := lebesgue_measure.
Variable (mean : R).
Hypothesis mean0 : (0 < mean)%R.

Hypothesis integrable_exponential : forall (m : R), (0 < m)%R ->
  mu.-integrable [set: _] (EFin \o (exponential_pdf m)).

Hypothesis integral_exponential_pdf : forall (m : R), (0 < m)%R ->
  (\int[mu]_x (exponential_pdf m x)%:E = 1)%E.

Local Notation exponential := (exponential (integral_exponential_pdf mean0)).

Let exponential0 : exponential set0 = 0%E.
Proof. by rewrite /exponential integral_set0. Qed.

Let exponential_ge0 A : (0 <= exponential A)%E.
Proof.
by rewrite /exponential integral_ge0//= => x _; rewrite lee_fin exponential_pdf_ge0.
Qed.

Let exponential_sigma_additive : semi_sigma_additive exponential.
Proof.
Admitted.

HB.instance Definition _ := isMeasure.Build _ _ _
  exponential exponential0 exponential_ge0 exponential_sigma_additive.

Let exponential_setT : exponential [set: _] = 1%E.
Proof. by rewrite /exponential integral_exponential_pdf. Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R exponential exponential_setT.

End exponential.
