From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
Require Import set_interval.
Require Import signed reals ereal topology normedtype sequences real_interval.
Require Import esum measure lebesgue_stieltjes_measure lebesgue_measure numfun.
Require Import realfun exp derive lebesgue_integral charge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section drestrict.
Context (R : realType).

Definition drestrict (a b : R) (f : R -> R)
 (f_c0 : {within `[a, b], continuous f})
 (f_nd0 : {in `[a, b] &, nondecreasing_fun f})
:= fun (x : R) =>
  if x < a then f a else
    if x < b then f x else f b.

End drestrict.

Section continuous_nondecreasing_is_cumulative.
Context (R : realType).
Variables (a b : R) (f : R -> R).

Hypothesis (f_c0 : {within `[a, b], continuous f}).
Hypothesis (f_nd0 : {in `[a, b] &, nondecreasing_fun f}).

Local Notation drf := (drestrict f_c0 f_nd0).

Let drf_nd : nondecreasing_fun drf.
Proof.
Admitted.

Let drf_rc : right_continuous drf.
Proof.
Admitted.

HB.instance Definition _ := isCumulative.Build R drf drf_nd drf_rc.
End continuous_nondecreasing_is_cumulative.

Section drestrict_finite_measure.
Context (R : realType).
Variables (a b : R) (f : R -> R).

Hypothesis (f_c0 : {within `[a, b], continuous f}).
Hypothesis (f_nd0 : {in `[a, b] &, nondecreasing_fun f}).

Local Notation drf := (drestrict f_c0 f_nd0).
Local Notation laf := (lebesgue_stieltjes_measure drf).

Let laf_finite : fin_num_fun laf.
Proof. Admitted.

HB.instance Definition _ := @isFinite.Build _ _ R laf laf_finite.

End drestrict_finite_measure.

Context (R : realType).

Local Notation mu := (@lebesgue_measure R).

Variables (a b : R).
Variable (f : R -> R).

Hypothesis (ab : a < b).
Hypothesis (cf : {within `[a, b], continuous f}).
Hypothesis (ndf : {in `[a, b] &, nondecreasing_fun f}).

Local Notation TVf := (fine \o ((total_variation a)^~ f)).

Let TVf_c0 : {within `[a, b], continuous TVf}.
Proof. Admitted.

Let TVf_nd0 : {in `[a, b] &, nondecreasing_fun TVf}.
Proof. Admitted.

Definition laf := (lebesgue_stieltjes_measure (drestrict TVf_c0 TVf_nd0)).

Let dlafdmu := (Radon_Nikodym [the charge _ _ of charge_of_finite_measure laf] mu).

Lemma continuous_nondecreasing_total_variation_radon_nikodym_derivative :
{in `[a, b] , (f =1 (fun x => f a + (fine \o dlafdmu) x)%R)}.
Proof.
Admitted.

Lemma integral_continuous_nondecreasing_itv :
  a < b ->
  {within `[a, b], continuous f} ->
  {in `[a, b] &, nondecreasing_fun f} ->
  mu (f @` `]a, b[) = ((f b)%:E - (f a)%:E)%E.
Proof.
move=> ab cf ndf.
rewrite -[LHS]mul1e.
rewrite -integral_cst /=.
rewrite (_: (\int[mu]_(_ in [set f x | x in `]a, b[]) 1)%E  = 
  (\int[mu]_(x in `]a, b[) dlafdmu x)%E).
Admitted.
