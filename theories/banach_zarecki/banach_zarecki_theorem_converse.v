From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean perm finmap.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions contra cardinality.
From mathcomp Require Import reals topology normedtype ereal sequences derive.
From mathcomp Require Import measure real_measure borel_hierarchy.
From mathcomp Require Import numfun realfun measurable_realfun.
From mathcomp Require Import absolute_continuity banach_zarecki_lemma2.
From mathcomp Require Import banach_zarecki_lemma3 banach_zarecki_lemma5.
From mathcomp Require Import banach_zarecki_lemma4 (* for contiguous intervals *).
From mathcomp Require Import mesh oscillation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Import MeasurableR.

Section ene6_converse.
Context {R : realType}.
Variables a b : R.
Hypotheses ab : a < b.

Local Notation mu := (@completed_lebesgue_measure R).

Variable f : R -> R.

Let H := fun x => fine (total_variation a ^~ f x).

(* lemma6(i) *)
Lemma ene6_converse :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] H -> lusinN `[a, b] f.
Proof.
move=> cf abf.
move=> lusinNH Z Zab/= mZ mZ0.
have muZ_lty : ((wlength idfun)^*%mu Z < +oo)%E.
  move: mZ0.
  rewrite /mu/=.
  (* TODO: lemma to avoid unfold *)
  rewrite /completed_lebesgue_stieltjes_measure.
  by rewrite /completed_measure_extension => ->.
move : muZ_lty => /(@lebesgue_measure_Gdelta_approx R Z).
move=> [G [G0oo ZG oG Gnonincreasing muZ]].
pose Z1 := `]a, b[ `&` \bigcap_i G i.
suff: mu (f @` Z1) = 0.
  move=> mfZ1.
  apply/eqP; rewrite eq_le measure_ge0 andbT.
  rewrite -mfZ1.
  rewrite le_outer_measure//.
  rewrite /Z1.
  apply: image_subset.
  rewrite -bigcapIr//.
  apply: sub_bigcap => i _.
  rewrite subsetI; split => //.
  admit.
have H1 : mu (H @` Z1) = mu (\bigcap_i (H @` (G i))) /\
       mu (\bigcap_i (H @` (G i))) = 0.
  split.
    rewrite completed_lebesgue_measureE.
    have := @measure_image_nondecreasing_fun R a b H ab _ G.
    (* mismatch Z1 should be an intersection of G's... *)
    admit.

(*      rewrite fine_le//.
      + apply/bounded_variationP => //.
        exact: bounded_variationl abf.
      + apply/bounded_variationP => //.
        exact: bounded_variationl abf.
      + apply: (total_variation_nondecreasing f) => //; rewrite ?in_itv/=.
        by rewrite xa/=; exact: xb.
        by rewrite ya/=; exact: yb.
    - exact: total_variation_continuous.
    - move=> k.*)

  admit.
have H2 : mu (H @` G i) @[i --> \oo] --> 0%E.
  admit.
pose G_ i := \bigcup_j (open_disjoint_itv (oG i) j).
have H3 i :
  mu (f @` Z1) = mu (f @` (\bigcup_j (Z1 `&` (open_disjoint_itv (oG i) j)))).
  admit.
have H4 i :
    (mu (f @` (\bigcup_j (Z1 `&` (open_disjoint_itv (oG i) j)))) <=
    \sum_(j <oo) (mu^* )%mu (f @` (Z1 `&` (open_disjoint_itv (oG i) j))))%E.
  admit.
have H5 i :
    (\sum_(j <oo) (mu^* )%mu (f @` (Z1 `&` (open_disjoint_itv (oG i) j))) <
    \sum_(j <oo) oscillation f (closure (open_disjoint_itv (oG i) j)))%E.
  admit.
have H6 i :
    (\sum_(j <oo) oscillation f (closure (open_disjoint_itv (oG i) j)) =
    mu (H @` G_ i))%E.
  admit.
apply/eqP; rewrite eq_le measure_ge0 andbT.
Admitted.

End ene6_converse.

(* ref: Theory of the Integral, Stanislaw Saks *)
Section Saks.
Context {R : realType}.

(* p.225, Chapter VII, Theorem 6.1 *)
Lemma abs_cont_lusinN (a b : R) (f : R -> R) :
  abs_cont a b f -> lusinN `[a, b] f.
Proof.

Abort.

End Saks.

Section BZ_converse.

Context {R : realType}.
Variables a b : R.
Hypotheses ab : a < b.

Local Notation mu := (@lebesgue_measure R).
Local Notation mue := ((@wlength R idfun)^*)%mu.

  

Theorem Banach_Zarecki_converse (f : R -> R) :
  abs_cont a b f ->
  [/\ {within `[a, b], continuous f},
  bounded_variation a b f &
  lusinN `[a, b] f].
Proof.
have muE : (@lebesgue_measure R) = (wlength idfun)^*%mu by [].
move=> acf.
have cf : {within `[a, b], continuous f}.
  apply/continuous_within_itvccP => //; split.
  - move=> x xab.
    apply/cvg_ballP => e e0.
    have [d'] := acf (PosNum e0).
    set d := minr (minr (x - a) (b - x)) (d'%:num / 4).
    have d0 : 0 < d.
      admit.
    set l := x - d.
    set r := x + d.
    have H : [/\ forall i : nat, (i < 1)%N ->
                      (l, r).1 < (l, r).2 /\ `](l, r).1, (l, r).2[ `<=` `[a, b],
       trivIset `I_1 (fun=> `](l, r).1, (l, r).2[%classic)
     & \sum_(k < 1) ((l, r).2 - (l, r).1) < d'%:num].
      split.
      + move=> i _ /=; split.
        admit.
(*
          rewrite gt_max !lt_min.
          rewrite andb_assoc -!andb_assoc; apply/and4P; split.
          * by [].
          * rewrite ltr_pDr//.
            by move: xab; rewrite in_itv/= => /andP[].
          * rewrite ltrBlDl ltr_pDl//.
            by move: xab; rewrite in_itv/= => /andP[].
          * by rewrite ler_ltD// gtrN.
        apply: subset_itv; rewrite bnd_simp.
*)
        admit.
(*
          by rewrite le_max lexx.
        by rewrite ge_min lexx.
*)
      + by rewrite II1; move=> ? ? -> -> /=.
      + rewrite big_ord1/=.
        rewrite -(subr0 r).
        rewrite -(subrr x).
        rewrite opprB (addrC x).
        rewrite addrA -(addrA _ x).
        rewrite (splitr d'%:num).
        have dd' : d < d'%:num / 2.
          admit.
        rewrite -(addrA x) subrKC.
        rewrite opprB subrKC.
        exact: ltrD.
    move/(_ 1%N (fun => (l, r)) H).
    rewrite big_ord1/= => frfle.
    exists d => //.
    move=> z/=.
  admit.
- admit.
- admit.
have bvf : bounded_variation a b f.
  admit.
split => //.
(* move to abs_cont_lusinN*)
(* lemma6_converse *)
apply: ene6_converse => //.
move=> X abX cmX.
(* lusinN is not necessary for completed lebesgue measure *)
rewrite completed_lebesgue_measureE muE.
move=> N0.
have [] := @lebesgue_measure_Gdelta_approx _ X.
  by rewrite N0.
move=> A [A0oo NA oA decA mAE].
apply/eqP; rewrite eq_le; apply/andP; split; last exact: outer_measure_ge0.
set TV : R -> \bar R := fun x => total_variation a x f.
apply: (@le_trans _ _ (mu (\bigcap_i ((fine \o TV) @` (A i))))).
(* lemma2 *)
  have mTVfoo : (mu ((fine \o TV) @` X) < +oo)%E.
    apply: (@le_lt_trans _ _ (mu `[(fine \o TV) a, (fine \o TV) b])).
      apply: le_outer_measure.
      apply: (@subset_trans _ ((fine \o TV) @` `[a, b])).
        exact: image_subset.
      apply: continuous_nondecreasing_image_itvcc.
      - exact: ltW.
      - exact: total_variation_continuous.
      move=> x y xab yab xy.
      rewrite -lee_fin !fineK.
      - move: xab; rewrite in_itv/= => /andP[ax xb].
        apply/bounded_variationP => //.
        exact: bounded_variationl bvf.
      - move: yab; rewrite in_itv/= => /andP[ay yb].
        apply/bounded_variationP => //.
        exact: bounded_variationl bvf.
      exact: total_variation_nondecreasing xab yab xy.
    rewrite lebesgue_measure_itv => //=.
    by case: ifPn => //; rewrite -EFinB ltry.
  rewrite (_: mue = mu)//.
  apply: le_outer_measure => y [x Xx <-] n _.
  exists x => //.
  exact: NA.
admit.
Admitted.

End BZ_converse.
