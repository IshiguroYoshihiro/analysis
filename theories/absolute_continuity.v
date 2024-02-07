From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences real_interval.
Require Import esum measure lebesgue_measure numfun lebesgue_integral.
Require Import realfun exp lebesgue_stieltjes_measure.

(**md**************************************************************************)
(* # Absolute Continuity                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.


Section Absolute_Continuous.
Context (R : realType).

(* this would be used in abs_cont_bounded_variation *)
Lemma itv_partition_undup_merge (a b : R) (s t : seq R) :
itv_partition a b s -> itv_partition a b t ->
itv_partition a b (undup (merge <%R s t)).
Proof.
Admitted.

Definition abs_cont (a b : R) (f : R -> R) := forall e : {posnum R},
  exists d : {posnum R}, forall (I : finType) (B : I -> R * R),
    (forall i, (B i).1 <= (B i).2 /\ `[(B i).1, (B i).2] `<=` `[a, b]) /\
      trivIset setT (fun i => `[(B i).1, (B i).2]%classic) /\
    \sum_(k in I) ((B k).2 - (B k).1) < d%:num ->
    \sum_(k in I) (f (B k).2 - f ((B k).1)) < e%:num.

Lemma abs_cont_bounded_variation (a b : R) (f : R -> R) :
abs_cont a b f -> bounded_variation a b f.
Proof.
Admitted.

End Absolute_Continuous.

(* TODO: move to topology.v *)
Section Gdelta.
Context (R : topologicalType).

Definition Gdelta (S : set R) :=
  exists A_ : (set R)^nat, (forall i, open (A_ i)) /\ S = \bigcap_i (A_ i).

Lemma open_Gdelta (S : set R) : open S -> Gdelta S.
Proof.
pose S_ (i : nat) := bigcap2 S setT i.
exists S_; split.
- move=> i.
  rewrite /S_ /bigcap2.
  case: ifP => // _.
  by case: ifP => // _; apply: openT.
- by rewrite bigcap2E setIT.
Qed.

End Gdelta.

Section Banach_Zarecki.
Context (R : realType).
Context (m := (@lebesgue_measure R)).
Context (a b : R) (ab : a < b).

Let Borel := @measurable _ R.

Let Lusin (f : R -> R) := (forall E : set R, m E = 0%E -> m (image E f) = 0%E).

Let H f x := total_variation a x f.

Lemma total_variation_Lusin (f : R -> R) :
{within `[a, b], continuous f}
  -> bounded_variation a b f
  -> Lusin (fun x => fine (H f x))
  -> Lusin f.
Proof.
Admitted.

Lemma Lusin_total_variation (f : R -> R) :
{within `[a, b], continuous f}
  -> bounded_variation a b f
  -> Lusin f
  -> Lusin (fun x => fine (H f x)).
Proof.
Admitted.

Let B (f : R -> R) := [set y | exists x, x \in `[a, b] /\ f@^-1` [set y] = [set x]].

Lemma nondecreasing_fun_cmplB_borel f :
{in `[a, b] &, {homo f : x y / x <= y}}
  -> Borel (`[f a, f b]%classic `\` (B f)).
Proof.
Admitted.

Lemma nondecreasing_fun_image_Gdelta_borel f (Z : set R) :
{in `[a, b] &, {homo f : x y / x <= y}}
  -> Z `<=` `]a, b[%classic
  -> Gdelta Z
  -> Borel [set f x | x in Z].
Proof.
Admitted.

Lemma nondecreasing_fun_image_measure (f : R -> R) (G_ : (set R)^nat) :
{in `[a, b] &, {homo f : x y / x <= y}}
  -> \bigcap_i G_ i `<=` `]a, b[%classic
  -> m (\bigcap_i (G_ i)) = \sum_(i \in setT) (m (G_ i)).
Proof.
Admitted.

Lemma Banach_Zarecki_increasing (f : R -> R) :
{within `[a, b], continuous f}
  -> {in `[a, b]  &, {homo f : x y / x <= y}}
  -> bounded_variation a b f
  -> Lusin f
  -> abs_cont a b f.
Proof.
move=> cf incf bvf Lf.
case: (EM (abs_cont a b f)) => //.
move/existsNP => [e0].
move/forallNP => nacf.
apply: False_ind.

have p2' (n : nat) : (0 < (1 / 2 ^ n)).
  admit.
pose p2 := p2' R.
pose d_ (n : nat) : {posnum R} := PosNum (p2 n).

have := (fun n => nacf (d_ n)).
move/(_ _)/existsNP.
move/choice.

Admitted.

Let H' (f : R -> R) (x : R) := fine (H f x).

(* Lemma total_variation_BV (f : R -> R) : *)
(* bounded_variation a b (H' f) -> bounded_variation a b f. *)
(* Proof. *)
(* move=> bvH'. *)
(* have able : a <= b. *)
(*   by apply/ltW. *)
(* apply/bounded_variationP => //. *)
(* rewrite ge0_fin_numE; last by apply: total_variation_ge0. *)
(* apply: (@le_lt_trans _ _ (total_variation a b (H' f))); last first. *)
(*   rewrite -ge0_fin_numE; last by apply: total_variation_ge0. *)
(*   by apply/bounded_variationP. *)
(* apply: ub_ereal_sup => xe /= [] x /[swap] <- {xe}. *)
(* rewrite /variations => /=. *)
(* move/cid2 => [] s itvs <-. *)
(* apply: ereal_sup_le. *)
(* exists (variation a b (H' f) s)%:E. *)
(*   move=> //. *)
(*   exists (variation a b (H' f) s) => //. *)
(*   exact: variations_variation. *)
(* rewrite !variation_next //. *)
(* elim: s itvs; first by move=> ?; rewrite !big_nil. *)
(* move=> h t IH ht. *)
(* rewrite /= !big_cons. *)
(* rewrite !EFinD. *)
(* rewrite lee_add => //. *)
(* - have ah : a <= h. *)
(*     admit. *)
(*   have hb : h <= b. *)
(*     admit. *)
(*   unlock => /=. *)
(*   rewrite !ifT => //. *)
(*   rewrite /H' /H total_variationxx fine0 subr0. *)
(*   rewrite [X in (_ <= X%:E)%E]ger0_norm; last by rewrite fine_ge0 // total_variation_ge0. *)
(*   (* BV f ? *) admit. *)
(* rewrite !big_seq. *)
(* apply: ler_sum => e eht. *)
(* pose ne := next (locked (h :: t)) e; fold ne. *)
(* have ae : a <= e. *)
(*   admit. *)
(* have ene : e <= ne. *)
(*   admit. *)
(* have neb : ne <= b. *)
(*   admit. *)
(* rewrite /H' /H (total_variationD _ ae) //; last first. *)
(*   admit. *)
(* rewrite fineD; last 2 first. *)
(*     (* BV f ? *) admit. *)
(*   admit. *)
(* rewrite addrAC subrr add0r. *)
(* Abort. *)

Lemma total_variation_AC (f : R -> R) :
bounded_variation a b f ->
abs_cont a b (H' f) -> abs_cont a b f.
Proof.
move=> bvH' acH' e.
have := acH' e.
move: (acH') => _ [d ac'H'].
exists d => I B trivB.
have := ac'H' I B trivB.
move: trivB => [/all_and2 [B21 Bab] [trivB sumBd sumHd]].
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
rewrite /H' /H.
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

Lemma TV_nondecreasing (f : R -> R) :
bounded_variation a b f -> {in `[a, b] &, {homo H' f : x y / x <= y}}.
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
rewrite /H (@total_variationD _ a y x) //; last first.
apply: lee_addl.
exact: total_variation_ge0.
Qed.

Lemma TV_bounded_variation (f : R -> R) :
bounded_variation a b f -> bounded_variation a b (H' f).
Proof.
move=> bvf.
apply/bounded_variationP; rewrite ?ltW //.
rewrite ge0_fin_numE; last by apply: total_variation_ge0; rewrite ltW.
rewrite nondecreasing_total_variation; rewrite ?ltW //; first exact: ltry.
exact: TV_nondecreasing.
Qed.

Theorem Banach_Zarecki (f : R -> R) :
{within `[a, b], continuous f} -> bounded_variation a b f
  -> Lusin f
  -> abs_cont a b f.
Proof.
move=> cf bvf Lf.
apply: total_variation_AC => //.
apply: Banach_Zarecki_increasing.
      exact: total_variation_continuous.
    exact: TV_nondecreasing.
  exact: TV_bounded_variation.
exact: Lusin_total_variation.
Qed.

End Banach_Zarecki.
