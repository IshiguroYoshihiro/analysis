From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences real_interval.
Require Import esum measure lebesgue_measure numfun lebesgue_integral.
Require Import realfun exp lebesgue_stieltjes_measure derive.

(**md**************************************************************************)
(* # Absolute Continuity                                                      *)
(* ```                                                                        *)
(*   Gdelta ==                                                                *)
(*   abs_cont ==                                                              *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.


(* TODO: move to topology.v *)
Section Gdelta.
Context (R : topologicalType).

Definition Gdelta (S : set R) :=
  exists2 A_ : (set R)^nat, (forall i, open (A_ i)) & S = \bigcap_i (A_ i).

Lemma open_Gdelta (S : set R) : open S -> Gdelta S.
Proof.
pose S_ i := bigcap2 S setT i.
exists S_.
- move=> i.
  rewrite /S_ /bigcap2.
  case: ifP => // _.
  by case: ifP => // _; apply: openT.
- by rewrite bigcap2E setIT.
Qed.

End Gdelta.

Section absolute_continuity.
Context {R : realType}.

Definition abs_cont (a b : R) (f : R -> R) := forall e : {posnum R},
  exists d : {posnum R}, forall n (B : 'I_n -> R * R),
    [/\ (forall i, (B i).1 <= (B i).2 /\ `[(B i).1, (B i).2] `<=` `[a, b]),
        trivIset setT (fun i => `[(B i).1, (B i).2]%classic) &
        \sum_(k < n) ((B k).2 - (B k).1) < d%:num] ->
    \sum_(k < n) (f (B k).2 - f ((B k).1)) < e%:num.

Lemma total_variation_AC a b (f : R -> R) : a < b ->
  bounded_variation a b f ->
  abs_cont a b (fine \o (total_variation a ^~ f)) -> abs_cont a b f.
Proof.
move=> ab bvH' acH' e.
have := acH' e.
move: (acH') => _ [d ac'H'].
exists d => n B trivB.
have := ac'H' n B trivB.
move: trivB => [/all_and2[B21 Bab]] trivB sumBd sumHd.
apply: (le_lt_trans _ sumHd).
apply: ler_sum => i iI.
have aB1 : a <= (B i).1.
  move: (Bab i).
  move/in1_subset_itv.
  move/(_ (fun x => a <= x)).
  apply.
    by move=> x; rewrite in_itv /= => /andP [].
  by rewrite in_itv /= B21 andbT.
have B2b : (B i).2 <= b.
  move: (Bab i).
  move/in1_subset_itv.
  move/(_ (fun x => x <= b)).
  apply.
    by move=> x; rewrite in_itv /= => /andP [].
  by rewrite in_itv /= B21 andTb.
have able : a <= b.
  by apply/ltW.
apply: (le_trans (ler_norm (f (B i).2 - f (B i).1))).
rewrite /=.
rewrite (@total_variationD _ a (B i).2 (B i).1 f) => //.
rewrite fineD; last 2 first.
- apply/bounded_variationP => //.
  by apply: (@bounded_variationl _ _ _ b) => //; first apply: (le_trans _ B2b).
- apply/bounded_variationP => //.
  apply: (bounded_variationl _ B2b) => //.
  by apply: (bounded_variationr aB1) => //; first apply: (le_trans _ B2b).
rewrite addrAC subrr add0r.
rewrite -[leLHS]add0r -ler_subr_addr.
rewrite -lee_fin.
rewrite EFinB.
rewrite fineK; last first.
  apply/bounded_variationP => //.
  apply: (bounded_variationl _ B2b) => //.
  by apply: (bounded_variationr aB1); first apply: (@le_trans _ _ (B i).2).
rewrite lee_subr_addr; last first.
  rewrite ge0_fin_numE; last exact: normr_ge0.
  exact: ltry.
rewrite add0e.
by apply: total_variation_ge.
Qed.

Lemma TV_nondecreasing a b (f : R -> R) :
  bounded_variation a b f ->
  {in `[a, b] &, {homo fine \o (total_variation a ^~ f) : x y / x <= y}}.
Proof.
move=> bvf x y xab yab xy.
have ax : a <= x.
  move: xab.
  rewrite in_itv /=.
  by move/andP => [].
have yb : y <= b.
  move: yab.
  rewrite in_itv /=.
  by move/andP => [].
rewrite fine_le => //.
    apply/bounded_variationP => //.
    apply: (@bounded_variationl _ a x b) => //.
    by apply: (le_trans xy).
  apply/bounded_variationP.
    by apply: (le_trans ax).
  apply: (bounded_variationl _ yb) => //.
  by apply: (le_trans ax).
rewrite  (@total_variationD _ a y x) //; last first.
apply: lee_addl.
exact: total_variation_ge0.
Qed.

Lemma TV_bounded_variation a b (f : R -> R) : a < b ->
  bounded_variation a b f -> bounded_variation a b (fine \o (total_variation a ^~ f)).
Proof.
move=> ab bvf.
apply/bounded_variationP; rewrite ?ltW //.
rewrite ge0_fin_numE; last by apply: total_variation_ge0; rewrite ltW.
rewrite nondecreasing_total_variation; rewrite ?ltW //; first exact: ltry.
exact: TV_nondecreasing.
Qed.

End absolute_continuity.

Section wip.
Context {R : realType}.

(* this would be used in abs_cont_bounded_variation *)
Lemma itv_partition_undup_merge (a b : R) (s t : seq R) :
  itv_partition a b s -> itv_partition a b t ->
  itv_partition a b (undup (merge <%R s t)).
Proof.
Abort.

Lemma abs_cont_bounded_variation (a b : R) (f : R -> R) :
  abs_cont a b f -> bounded_variation a b f.
Proof.
Abort.

End wip.

Section lusinN.
Context {R : realType}.
Let mu := @lebesgue_measure R.

Definition lusinN (A : set R) (f : R -> R) :=
  forall E, E `<=` A -> measurable E -> mu E = 0 -> mu (f @` E) = 0.

Definition abs_contN (a b : R) (f : R -> R) :=
  [/\ {within `[a, b]%classic, continuous f},
      bounded_variation a b f &
      lusinN `[a ,b]%classic f].

Fail Lemma lusinN_total_variation a b f : abs_contN a b f ->
  lusinN `[a, b]%classic (total_variation a ^~ f).

Lemma abs_contN_dominates a b (f : cumulative R) : abs_contN a b f ->
  mu `<< lebesgue_stieltjes_measure f.
Abort.

Fail Lemma differentiable_lusinN a b f : {in `]a, b[%classic, differentiable f} ->
  lusinN `]a, b[%classic f.

End lusinN.

Section Banach_Zarecki.
Context (R : realType).
Context (m := (@lebesgue_measure R)).
Context (a b : R) (ab : a < b).

Lemma total_variation_Lusin (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] (fun x => fine ((total_variation a ^~ f) x)) ->
  lusinN `[a, b] f.
Proof.
Admitted.

Lemma Lusin_total_variation (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] f ->
  lusinN `[a, b] (fun x => fine (total_variation a ^~ f x)).
Proof.
Admitted.

Let increasing_points (f : R -> R) :=
  [set y | exists x, x \in `[a, b] /\ f@^-1` [set y] = [set x]].

Lemma nondecreasing_fun_setD_measurable f :
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  measurable (`[f a, f b]%classic `\` increasing_points f).
Proof.
Abort.

Lemma nondecreasing_fun_image_Gdelta_measurable (f : R -> R) (Z : set R) :
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  Z `<=` `]a, b[%classic ->
  Gdelta Z ->
  measurable (f @` Z).
Proof.
Abort.

Lemma nondecreasing_fun_image_measure (f : R -> R) (G_ : (set R)^nat) :
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  \bigcap_i G_ i `<=` `]a, b[%classic ->
  m (\bigcap_i (G_ i)) = \sum_(i \in setT) (m (G_ i)).
Proof.
Abort.

Lemma Banach_Zarecki_increasing (f : R -> R) :
  {within `[a, b], continuous f} ->
  {in `[a, b]  &, {homo f : x y / x <= y}} ->
  bounded_variation a b f ->
  lusinN `[a, b] f ->
  abs_cont a b f.
Proof.
move=> cf incf bvf lf; apply: contrapT => /existsNP[e0] /forallNP fe0.
have {fe0} : forall d : {posnum R},
    exists n, exists B : 'I_n -> R * R,
      [/\ (forall i, (B i).1 <= (B i).2 /\ `[(B i).1, (B i).2] `<=` `[a, b]),
          trivIset setT (fun i => `[(B i).1, (B i).2]%classic),
          \sum_(k < n) ((B k).2 - (B k).1) < d%:num &
          \sum_(k < n) (f (B k).2 - f (B k).1) >= e0%:num].
  move=> d; have {fe0} := fe0 d.
  move=> /existsNP[n] /existsNP[B] /not_implyP[] [H1 H2 H3 H4].
  by exists n, B; split => //; rewrite leNgt; apply/negP.
move=> /choice[n_0 ab_0].
pose delta_0 (i : nat) : R := (2 ^+ i)^-1.
have delta_0_ge0 (i : nat) : 0 < (2 ^+ i)^-1 :> R by rewrite invr_gt0 exprn_gt0.
pose delta_ (i : nat) : {posnum R} := PosNum (delta_0_ge0 i).
pose n_ i := n_0 (delta_ i).
pose ab_ i : 'I_(n_ i) -> R * R := projT1 (cid (ab_0 (delta_ i))).
have d_prop i : \sum_(k < n_ i) (((ab_ i) k).2 - ((ab_ i) k).1) < delta_0 i.
  by rewrite /ab_; case: cid => ? [].
have e0_prop i : \sum_(k < n_ i) (f (((ab_ i) k).2) - f ((ab_ i) k).1) >= e0%:num.
  by rewrite /ab_; case: cid => ? [].
pose E_ i := \big[setU/set0]_(k < n_ i) `]((ab_ i) k).2, ((ab_ i) k).1[%classic.
pose G_ i := \bigcup_(j in [set j | (j >= i)%N]) E_ j.
pose A := \bigcap_i (G_ i).
have mA0 : lebesgue_measure A = 0.
  rewrite /A.
  admit.
have mfA0 := lebesgue_measure (f @` A) = 0.
  (* use lf *)
  admit.
Admitted.

Theorem Banach_Zarecki (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] f ->
  abs_cont a b f.
Proof.
move=> cf bvf Lf.
apply: total_variation_AC => //.
apply: Banach_Zarecki_increasing.
- exact: total_variation_continuous.
- exact: TV_nondecreasing.
- exact: TV_bounded_variation.
- exact: Lusin_total_variation.
Qed.

End Banach_Zarecki.
