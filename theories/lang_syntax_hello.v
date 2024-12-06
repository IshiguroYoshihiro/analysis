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
  let "x" := Sample {exp_normal_1 (exp_real 0)} in
  let "y" := Sample {exp_normal_1 [#{"x"}]} in
  let "_" := {guard_real "y" y0} in
  let "z" := Sample {exp_normal_1 [#{"x"}]} in
  return #{"z"}].

Definition helloRight (y0 : R) : @exp R _ [::] _ :=
 [Normalize
  let "x" := Sample {exp_normal_1 (exp_real 0)} in
  let "_" := Score {(exp_pow_real (expR 1)
    ([{0}:R] - exp_pow 2 ([{y0}:R] - [#{"x"}])) * [{2^-1}:R]) *
    [{(Num.sqrt 2 * pi)^-1}:R]} in
  let "z" := Sample {exp_normal_1 [#{"x"}]} in
  return #{"z"}].

  return {1}:Nat <= #{"x"}].


  let "x" := Sample {exp_binomial 8 [#{"p"}]} in
  let "_" := {guard "x" 5} in
  let "y" := Sample {exp_binomial 3 [#{"p"}]} in
  return {1}:N <= #{"y"}].
 *)
 End hello_programs.

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


Definition guard {g} str n : @exp R P [:: (str, _) ; g] _ :=
  [if #{str} == {n}:N then return TT else Score {0}:R].
