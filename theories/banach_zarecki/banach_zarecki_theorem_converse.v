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

Section lemma6_converse.
Context {R : realType}.
Variables a b : R.
Hypotheses ab : a < b.

Local Notation mu := (@completed_lebesgue_measure R).

Variable f : R -> R.

Let H := fun x => fine (total_variation a ^~ f x).

(* lemma6(i) *)
Lemma total_variation_Lusin :
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

End lemma6_converse.

Section lemmas.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Local Notation mue := ((@wlength R idfun)^*)%mu.

Lemma image_lebesgue_measure_Gdelta_approx (f : R -> R) (Z : set R) :
  (mue Z < +oo)%E ->
  exists U : (set R)^nat, [/\ (lebesgue_measure (U 0%N) < +oo)%E,
    (forall k, Z `<=` U k), (forall k, open (U k)),
    {homo U : n m / (n <= m)%N >-> (m <= n)%O} &
    mue (f @` Z) = mue (\bigcap_k U k)].
Proof.
move=> Zoo.
(* Z has Gdelta approx {U i}_i  *)
have [U [U0oo ZU oU decU muZE]] := lebesgue_measure_Gdelta_approx Zoo.
have [|] := pselect (mue (f @` Z) = +oo)%E.
  
(* forall i, f @` (U i) has Gdelta approx {V i j}_j *)

(* *)
Abort.

End lemmas.

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
  admit.
have bvf : bounded_variation a b f.
  admit.
split => //.
(* lemma6_converse *)
apply: total_variation_Lusin => //.
move=> X abX cmX.
(* lusinN is not necessary for completed lebesgue measure *)
rewrite completed_lebesgue_measureE muE.
move=> N0.
have [] := @lebesgue_measure_Gdelta_approx _ X.
  by rewrite N0.
move=> A [A0oo NA oA decA mAE].
apply/eqP; rewrite eq_le; apply/andP; split; last exact: outer_measure_ge0.
apply: (@le_trans _ _ (mu (\bigcap_i (f @` (A i))))).
(* lemma2 *)
  set TV : R -> \bar R := fun x => total_variation a x f.
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
  
  have mA i : (R.-open).-measurable (A i) by exact: open_measurable.
  have/cvg_lim := (@cvg_measure_bigcap _ _ _ mu A mA A0oo).


rewrite -muE.
admit.
Admitted.

End BZ_converse.
