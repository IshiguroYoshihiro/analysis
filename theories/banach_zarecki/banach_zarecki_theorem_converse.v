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

Section lemmas.
Context {R : realType}.

Lemma le_bounded_variation (a b : R) f : b <= a -> bounded_variation a b f.
Proof.
rewrite le_eqVlt => /predU1P[->|ba].
  exact: bounded_variationxx.
exists (variation a b f [:: a]).
move=> /= r [s].
move/itv_partition_le.
by rewrite leNgt ba.
Qed.

End lemmas.

Section banachS.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Implicit Types (a b : R) (f : R -> R) (P : set R).

(* Banach's (S) condition *)
(* ref: Vasile Ene, Real Functions - Current Topics
        p.71, Chapter 2, Section 2.18, Definition 2.18.3,
        Stanislaw Saks, Theory of the Integral, second revised edition, *)

Definition banachS P f := forall e : R, 0 < e ->
  exists d, 0 < d /\
   forall Z : set R, Z `<=` P -> (mu Z < d%:E)%E -> (mu (f @` Z) < e%:E)%E.

Definition banachS_measurable P f := forall e : R, 0 < e ->
  exists d, 0 < d /\
   forall Z : set R, Z `<=` P -> R.-open.-measurable P ->
    (mu Z < d%:E)%E -> (mu (f @` Z) < e%:E)%E.

Lemma banachSP P f : R.-open.-measurable P ->
 (banachS P f <-> banachS_measurable P f).
Proof.
move=> mA; split=> hf r r0.
- have [d [d0 bd]] := hf r r0.
  exists d; split => // Z ZP mP Zd.
  exact: bd.
have [/= d [d0 bd]] := hf r r0.
exists d; split => // Z ZP Zd.
have Zoo : (mu (f @` Z) < +oo)%E.
(*
  by apply: (lt_trans Zd); rewrite ltry.

have [A [A0oo ZA oA ndA muZE]] := lebesgue_measure_Gdelta_approx Zoo.
rewrite /mu/lebesgue_stieltjes_measure/measure_extension.
rewrite muZE.
move=> /null_approx[H mH [EH H0]].
  have mAH : R.-open.-measurable (A `&` H) by exact: measurableI.
  have muAH : mu (A `&` H) = 0%E.
    by apply/eqP; rewrite eq_le measure_ge0 andbT -H0 le_measure ?inE//.
  apply/eqP; rewrite eq_le measure_ge0 andbT.
  rewrite -(hf _ (@subIsetl _ A H) mAH muAH).
  rewrite le_outer_measure//.
  apply: image_subset => x Ex.
  by split; [exact: EA | exact: EH].
- by move=> _; exact: hf EA.
*)
Abort.

End banachS.

Section ene6_converse.
Context {R : realType}.
Variables a b : R.
Hypotheses ab : a < b.

Local Notation mu := (@lebesgue_measure R).

Variable f : R -> R.

Let H := fun x => fine (total_variation a ^~ f x).

(* lemma6(i) *)
Lemma ene6_converse :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  measurable_lusinN `[a, b] H -> measurable_lusinN `[a, b] f.
Proof.
move=> cf abf.
move=> lusinNH Z Zab/= mZ mZ0.
have muZ_lty : ((wlength idfun)^*%mu Z < +oo)%E.
  move: mZ0.
  rewrite /mu/=.
  rewrite /lebesgue_stieltjes_measure.
  by rewrite /measure_extension => ->.
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
  abs_cont a b f -> measurable_lusinN `[a, b] f.
Proof.

Abort.

End Saks.

Section BZ_converse.

Context {R : realType}.
Variables a b : R.
Implicit Type (f : R -> R).

Lemma abs_cont_continuous f : abs_cont a b f -> {within `[a, b], continuous f}.
Proof.
have [|] := leP b a.
  rewrite le_eqVlt => /predU1P[|].
    move=> -> _.
    rewrite set_itv1.
    exact: continuous_subspace1.
  move=> ba _.
  rewrite set_itv_ge.
    by rewrite bnd_simp -ltNge.
  exact: continuous_subspace0.
move=> ab acf.
apply/continuous_within_itvccP => //; split.
- move=> x xab.
  apply/cvg_ballP => e e0.
  have [d'] := acf (PosNum e0).
  set d := minr (minr (x - a) (b - x)) (d'%:num / 4).
  have d0 : 0 < d.
    rewrite !lt_min -andb_assoc; apply/and3P; split.
    + rewrite subr_gt0.
      by move: xab; rewrite in_itv/= => /andP[].
    + rewrite subr_gt0.
      by move: xab; rewrite in_itv/= => /andP[].
    by rewrite pmulr_lgt0.
  have dd' : d < d'%:num.
    rewrite gt_min; apply/orP; right.
    rewrite gtr_pMr// invf_lt1//.
    by rewrite (_ : 1 = 1%:R)// ltr_nat.
  set l := x - d.
  set r := x + d.
  have al : a <= l.
    rewrite lerBrDr -lerBrDl.
    by rewrite !ge_min lexx.
  have rb : r <= b.
    rewrite -lerBrDl.
    by rewrite !ge_min lexx orbT.
  have H : [/\ forall i : nat, (i < 1)%N ->
                      (l, r).1 < (l, r).2 /\ `](l, r).1, (l, r).2[ `<=` `[a, b],
       trivIset `I_1 (fun=> `](l, r).1, (l, r).2[%classic)
     & \sum_(k < 1) ((l, r).2 - (l, r).1) < d'%:num].
    split.
    + move=> i _ /=; split.
        by rewrite ler_ltD// gtrN.
      apply: subset_itv; rewrite bnd_simp.
        by rewrite lerBDl -lerBDr !ge_min lexx.
      by rewrite -lerBDl !ge_min lexx orbT.
    + rewrite II1.
      by have := (@trivIset1 _ _ _ (fun=> `](l, r).1, (l, r).2[%classic)).
    rewrite big_ord1/=.
    rewrite /r (addrC x) addrKA opprK (splitr d'%:num) -!mulr2n.
    rewrite ltr_wMn2r//.
    apply: (@le_lt_trans _ _ (d'%:num / 4)).
      by rewrite ge_min lexx orbT.
    by rewrite ltr_pM2l// ltf_pV2 ?posrE// ltr_nat.
  move=> acfe.
  exists d => //.
  move=> z/=.
  rewrite ltr_norml.
  rewrite ltrBrDl ltrBlDr -/r => /andP[zr].
  rewrite ltrBlDr -ltrBlDl -/l => lz.
  rewrite /ball/=.
  have [|] := leP z x.
    rewrite le_eqVlt => /predU1P[<-|zx].
      by rewrite subrr normr0.
    move: (acfe 1%N (fun => (z, x))).
    rewrite !big_ord1/=; apply; split.
    + move=> _ _; split => //.
      apply: subset_itv; rewrite bnd_simp.
        exact/ltW/(le_lt_trans al lz).
      apply: ltW.
      by move: xab; rewrite in_itv/= => /andP[].
    + rewrite II1.
      by have := (@trivIset1 _ _ _ (fun => _)).
    apply: lt_trans dd'.
    by rewrite ltrBlDl -ltrBlDr.
  move=> xz.
  rewrite distrC.
  have := (acfe 1%N (fun => (x, z))).
  rewrite !big_ord1/=; apply; split.
  + move=> _ _; split => //.
    apply: subset_itv; rewrite bnd_simp.
      apply: ltW.
      by move: xab; rewrite in_itv/= => /andP[].
    exact/ltW/(lt_le_trans zr rb).
  + by rewrite II1; have  := (@trivIset1 _ _ _ (fun => _)).
    apply: lt_trans dd'.
    by rewrite ltrBlDl.
- apply/cvg_at_rightP => u [altu cvgua].
  apply/cvg_ballP => e e0.
  have [d acfe] := acf (PosNum e0).
  near=> N.
  rewrite /ball/= distrC.
  move: (acfe 1%N (fun => (a, u N))).
  rewrite !big_ord1/=; apply; split.
  + move=> ? _; split => //.
    apply: subset_itv; rewrite bnd_simp//.
    near: N.
    exact: (cvgr_le _ cvgua).
  + rewrite II1.
    exact: trivIset1.
  rewrite ltrBlDl.
  near: N.
  apply: (cvgr_lt _ cvgua).
    by rewrite ltrDl.
- apply/cvg_at_leftP => u [ultb cvgub].
  apply/cvg_ballP => e e0.
  have [d acfe] := acf (PosNum e0).
  near=> N.
  rewrite /ball/=.
  move: (acfe 1%N (fun => (u N, b))).
  rewrite !big_ord1/=; apply; split.
  + move=> ? _; split => //.
    apply: subset_itv; rewrite bnd_simp//.
    near: N.
    exact: (cvgr_ge _ cvgub).
  + rewrite II1.
    exact: trivIset1.
  rewrite ltrBlDl -ltrBlDr.
  near: N.
  apply: (cvgr_gt _ cvgub).
  by rewrite ltrBlDr ltrDl.
Unshelve. all: end_near. Qed.

Lemma abs_cont_bounded_variation f :
  abs_cont a b f -> bounded_variation a b f.
Proof.
move=> acf.
have [|ab] := leP b a.
  exact: le_bounded_variation.
have aleb := ltW ab.
apply/bounded_variationP => //.
rewrite ge0_fin_numE.
  exact: total_variation_ge0.

Admitted.

Local Notation mu := (@lebesgue_measure R).
Local Notation mue := ((@wlength R idfun)^*)%mu.

Theorem Banach_Zarecki_converse (f : R -> R) :
  abs_cont a b f ->
  [/\ {within `[a, b], continuous f},
  bounded_variation a b f &
  measurable_lusinN `[a, b] f].
Proof.
have muE : (@lebesgue_measure R) = (wlength idfun)^*%mu by [].
move=> acf.
have cf : {within `[a, b], continuous f}.
  exact: abs_cont_continuous.
have bvf : bounded_variation a b f.
  exact: abs_cont_bounded_variation.
split => //.
have [|ab] := leP b a.
  admit.
(* move to abs_cont_lusinN*)
(* lemma6_converse *)
apply: ene6_converse => //.
move=> X abX cmX.
(* lusinN is not necessary for completed lebesgue measure *)
rewrite muE.
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
