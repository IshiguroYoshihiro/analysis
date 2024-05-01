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

Section lebesgue_stieltjes_measure_itv.
Variable R : realType.
Variable f : cumulative R.

Let lebesgue_stieltjes_measure_itvoc (a b : R) :
  (lebesgue_stieltjes_measure f (`]a, b] : set R) =
  wlength f `]a, b])%classic.
Proof.
rewrite /lebesgue_measure/= /lebesgue_stieltjes_measure/= /measure_extension/=.
by rewrite measurable_mu_extE//; exact: is_ocitv.
Qed.

Let lebesgue_stieltjes_measure_itvoo_subr1 (a : R) :
  lebesgue_stieltjes_measure f (`]a - 1, a[%classic : set R)
     = ((f a)%:E - (f (a - 1))%:E)%E.
Proof.
rewrite itv_bnd_open_bigcup//; transitivity (limn ((lebesgue_stieltjes_measure f)
 \o (fun k => `]a - 1, a - k.+1%:R^-1]%classic : set R))).
  apply/esym/cvg_lim => //; apply: nondecreasing_cvg_mu.
  - by move=> ?; exact: measurable_itv.
  - by apply: bigcup_measurable => k _; exact: measurable_itv.
  - move=> n m nm; apply/subsetPset => x /=; rewrite !in_itv/= => /andP[->/=].
    by move/le_trans; apply; rewrite lerB// ler_pV2 ?ler_nat//;
      rewrite inE ltr0n andbT unitfE.
(* right continuity of f *)
Admitted.

Lemma lebesgue_stieltjes_measure_set1 (a : R) : lebesgue_stieltjes_measure f [set a] = 0%E.
Proof.
suff : (lebesgue_stieltjes_measure f (`]a - 1, a]%classic%R : set R) =
        lebesgue_stieltjes_measure f (`]a - 1, a[%classic%R : set R) +
        lebesgue_stieltjes_measure f [set a])%E.
  rewrite lebesgue_stieltjes_measure_itvoo_subr1 lebesgue_stieltjes_measure_itvoc => /eqP.
  rewrite wlength_itv lte_fin ltrBlDr ltrDl ltr01.
  rewrite [in X in X == _]/= EFinN -[X in _ == X]addeC.
  by rewrite -sube_eq ?fin_num_adde_defl// subee// => /eqP.
rewrite -setUitv1// ?bnd_simp; last by rewrite ltrBlDr ltrDl.
rewrite measureU //; apply/seteqP; split => // x []/=.
by rewrite in_itv/= => + xa; rewrite xa ltxx andbF.
Qed.

Let lebesgue_stieltjes_measure_itvoo (a b : R) :
  (lebesgue_stieltjes_measure f (`]a, b[ : set R) =
   wlength f `]a, b[)%classic.
Proof.
have [ab|ba] := ltP a b; last by rewrite set_itv_ge ?measure0// -leNgt.
have := lebesgue_stieltjes_measure_itvoc a b.
rewrite 2!wlength_itv => <-; rewrite -setUitv1// measureU//.
- by have /= -> := lebesgue_stieltjes_measure_set1 b; rewrite adde0.
- by apply/seteqP; split => // x [/= + xb]; rewrite in_itv/= xb ltxx andbF.
Qed.

Let lebesgue_stieltjes_measure_itvcc (a b : R) :
  (lebesgue_stieltjes_measure f (`[a, b] : set R) =
   wlength f `[a, b])%classic.
Proof.
have [ab|ba] := leP a b; last by rewrite set_itv_ge ?measure0// -leNgt.
have := lebesgue_stieltjes_measure_itvoc a b.
rewrite 2!wlength_itv => <-; rewrite -setU1itv// measureU//.
- by have /= -> := lebesgue_stieltjes_measure_set1 a; rewrite add0e.
- by apply/seteqP; split => // x [/= ->]; rewrite in_itv/= ltxx.
Qed.

Let lebesgue_stieltjes_measure_itvco (a b : R) :
  (lebesgue_stieltjes_measure f (`[a, b[ : set R) =
   wlength f `[a, b[)%classic.
Proof.
have [ab|ba] := ltP a b; last by rewrite set_itv_ge ?measure0// -leNgt.
have := lebesgue_stieltjes_measure_itvoo a b.
rewrite 2!wlength_itv => <-; rewrite -setU1itv// measureU//.
- by have /= -> := lebesgue_stieltjes_measure_set1 a; rewrite add0e.
- by apply/seteqP; split => // x [/= ->]; rewrite in_itv/= ltxx.
Qed.

Let lebesgue_stieltjes_measure_itv_bnd (x y : bool) (a b : R) :
  lebesgue_stieltjes_measure f ([set` Interval (BSide x a) (BSide y b)] : set R) =
  wlength f [set` Interval (BSide x a) (BSide y b)].
Proof.
by move: x y => [|] [|]; [exact: lebesgue_stieltjes_measure_itvco |
  exact: lebesgue_stieltjes_measure_itvcc |
  exact: lebesgue_stieltjes_measure_itvoo |
  exact: lebesgue_stieltjes_measure_itvoc].
Qed.

(* (* conflict to wlength_itv *) *)
(* (* do after remove er_map in definition of wlength *) *)

(* (* Let cumulative_limnatR : lim (((f (k%:R))%:E : \bar R) @[k --> \oo]) = +oo%E. *) *)
(* (* Proof. apply/cvg_lim => //. ; apply/cvgenyP. Qed. *) *)

(* Let lebesgue_stieltjes_measure_itv_bnd_infty x (a : R) : *)
(*   lebesgue_stieltjes_measure f ([set` Interval (BSide x a) +oo%O] : set R) = *)
(*      (lim (((f (a + k%:R))%:E : \bar R) @[k --> \oo]) - (f a)%:E)%E. *)
(* Proof. *)
(* rewrite itv_bnd_infty_bigcup; transitivity (limn ((lebesgue_stieltjes_measure f) \o *)
(*     (fun k => [set` Interval (BSide x a) (BRight (a + k%:R))] : set R))). *)
(*   apply/esym/cvg_lim => //; apply: nondecreasing_cvg_mu. *)
(*   + by move=> k; exact: measurable_itv. *)
(*   + by apply: bigcup_measurable => k _; exact: measurable_itv. *)
(*   + move=> m n mn; apply/subsetPset => r/=; rewrite !in_itv/= => /andP[->/=]. *)
(*     by move=> /le_trans; apply; rewrite lerD// ler_nat. *)
(* rewrite (_ : _ \o _ = (fun k => (f (a + k%:R) - f a)%:E)). *)
(*   admit. *)
(* apply/funext => n /=; rewrite lebesgue_stieltjes_measure_itv_bnd wlength_itv/=. *)
(* rewrite lte_fin;  have [->|n0] := eqVneq n 0%N; last first. *)
(*   rewrite EFinD ifT //. *)
(*   admit. *)
(* by rewrite ifF addr0 ?subrr. *)
(* Admitted. *)

(* Let lebesgue_stieltjes_measure_itv_infty_bnd y (b : R) : *)
(*   lebesgue_stieltjes_measure f ([set` Interval -oo%O (BSide y b)] : set R) = *)
(*     ((f b)%:E - lim (((f (b - k%:R))%:E : \bar R) @[k --> \oo]))%E. *)
(* Proof. *)
(* rewrite itv_infty_bnd_bigcup; transitivity (limn ((lebesgue_stieltjes_measure f) \o *)
(*     (fun k => [set` Interval (BLeft (b - k%:R)) (BSide y b)] : set R))). *)
(*   apply/esym/cvg_lim => //; apply: nondecreasing_cvg_mu. *)
(*   + by move=> k; exact: measurable_itv. *)
(*   + by apply: bigcup_measurable => k _; exact: measurable_itv. *)
(*   + move=> m n mn; apply/subsetPset => r/=; rewrite !in_itv/= => /andP[+ ->]. *)
(*     by rewrite andbT; apply: le_trans; rewrite lerB// ler_nat. *)
(* rewrite (_ : _ \o _ = (fun k : nat => ((f b)%:E) - (f (b - k%:R))%:E)%E). *)
(*   admit. *)
(* apply/funext => n /=; rewrite lebesgue_stieltjes_measure_itv_bnd wlength_itv/= lte_fin. *)
(* have [->|n0] := eqVneq n 0%N; last first. *)
(*   rewrite ifT //. *)
(*   admit. *)
(* by rewrite ifF ?subr0 // -EFinD subrr. *)
(* Admitted. *)

(* Let lebesgue_stieltjes_measure_itv_infty_infty : *)
(*   lebesgue_stieltjes_measure f ([set` Interval -oo%O +oo%O] : set R) = *)
(*     (lim (((f k%:R)%:E : \bar R) @[k --> \oo]) - lim (((f (- k%:R))%:E : \bar R) @[k --> \oo]))%E. *)
(* Proof. *)
(* rewrite set_itv_infty_infty -(setUv (`]-oo, 0[)) setCitv. *)
(* rewrite [X in _ `|` (X `|` _) ]set_itvE set0U measureU//; last first. *)
(*   apply/seteqP; split => //= x [] /= /[swap]. *)
(*   by rewrite !in_itv/= andbT ltNge => ->//. *)
(* rewrite [X in (X + _)%E]lebesgue_stieltjes_measure_itv_infty_bnd. *)
(* rewrite [X in (_ + X)%E]lebesgue_stieltjes_measure_itv_bnd_infty. *)
(* under eq_fun do rewrite sub0r. *)
(* rewrite addeCA. *)
(* under eq_fun do rewrite add0r. *)
(* by rewrite addeAC subee // sub0e. *)
(* Qed. *)

(* (* Lemma lebesgue_stieltjes_measure_itv (i : interval R) : *) *)
(* (*   lebesgue_stieltjes_measure f ([set` i] : set R) = *) *)
(* (*   (if i.1 < i.2 then (f (i.2 : R) - (f (i.1 : R)))%E else 0)%E. *) *)
(* (* Proof. *) *)
(* (* move: i => [[x a|[|]]] [y b|[|]]. *) *)
(* (*   by rewrite lebesgue_measure_itv_bnd wlength_itv. *) *)
(* (* - by rewrite set_itvE ?measure0. *) *)
(* (* - by rewrite lebesgue_measure_itv_bnd_infty/= ltry. *) *)
(* (* - by rewrite lebesgue_measure_itv_infty_bnd/= ltNyr. *) *)
(* (* - by rewrite set_itvE ?measure0. *) *)
(* (* - by rewrite lebesgue_measure_itv_infty_infty. *) *)
(* (* - by rewrite set_itvE ?measure0. *) *)
(* (* - by rewrite set_itvE ?measure0. *) *)
(* (* - by rewrite set_itvE ?measure0. *) *)
(* (* Qed. *) *)

Lemma lebesgue_stieltjes_measure_bounded_itv (x y : R) (b b' : bool) :
  lebesgue_stieltjes_measure f [set` (Interval (BSide b x) (BSide b' y))] =
    (if (x < y)%R then (f y - f x)%:E else 0)%E.
Proof. by rewrite lebesgue_stieltjes_measure_itv_bnd wlength_itv. Qed.

End lebesgue_stieltjes_measure_itv.

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
rewrite (_: (\int[mu]_(_ in f @` `]a, b[) 1)%E  = 
  (\int[mu]_(x in `]a, b[) dlafdmu x)%E).
rewrite -Radon_Nikodym_integral /=.
rewrite /lebesgue_stieltjes_measure /=.
rewrite wlength_itv.
Admitted.
