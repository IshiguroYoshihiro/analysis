From HB Require Import structures.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import cardinality.
From mathcomp Require Import reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure realfun.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import borel_hierarchy absolute_continuity.
From mathcomp Require Import banach_zarecki_lemma2.
From mathcomp Require Import lebesgue_measure_extra.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 3)                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ene3.
Context {R : realType} (a b : R).
Hypothesis ab : a < b.
Import MeasurableR.
Local Notation mu := (@lebesgue_measure R).

(* lemma3 (easy direction) *)
Lemma Lusin_image_measure0 (f : R -> R) :
  {within `[a, b], continuous f} ->
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  lusinN `[a, b] f ->
  forall Z : set R, [/\ Z `<=` `[a, b]%classic,
      compact Z &
      mu Z = 0] ->
      mu (f @` Z) = 0.
Proof.
move=> cf ndf lusinNf Z [Zab cZ muZ0].
have /= mZ : (wlength idfun)^*%mu.-cara.-measurable Z.
  apply: sub_caratheodory.
  rewrite RGenOpenSets.measurableE//.
  by apply: compact_measurable => //.
exact: (lusinNf Z Zab mZ muZ0).
Qed.

Let measurable_image_setI_set1 (f : R -> R) (A : set R) (x : R) :
  measurable (f @` (A `&` [set x])).
Proof.
rewrite setI1; case: ifP; rewrite ?image_set0// image_set1 => _.
exact: measurable_set1.
Qed.

Let measurable_setD1 (A : set R) (x : R) :
  measurable A -> measurable (A `\ x).
Proof.
move=> mA.
rewrite setDE.
apply: measurableI => //.
apply: measurableC.
exact: measurable_set1.
Qed.

Let image_setD1 (f : R -> R) (A : set R) (x : R) :
(forall a, (A `\ x) a -> f a != f x) ->
  f @` (A `\ x) = (f @` A) `\ f x.
Proof.
move=> H.
rewrite eqEsubset; split.
  move=> _ [z [Az /= zx] <-]; split; first by exists z.
  apply/eqP; exact: H.
move=> _ [[z Az <-] /= fzx].
exists z => //; split => //.
move=> zx; apply: fzx.
by f_equal.
Qed.

Let not_image_setD1 (f : R -> R) (A : set R) (x : R) :
 ~ (forall a, (A `\ x) a -> f a != f x) ->
  f @` (A `\ x) = (f @` A).
Proof.
move=> H.
rewrite eqEsubset; split.
  apply: image_subset.
  exact: subDsetl.
have [Ax|nAx] := pselect (A x); last by rewrite not_setD1.
rewrite -{1}(setD1K Ax).
move=> y [z + <-].
case.
  move->.
  move: H.
  move/existsNP => [t].
  move/not_implyP => [[At /= tx]].
  move/negP/negPn/eqP => ftx.
  by exists t.
move=> [Az /= zx].
by exists z.
Qed.

Let measurable_image_setD1 (f : R -> R) (A : set R) (x : R) :
  measurable (f @` A) ->
  measurable (f @` (A `\ x)).
Proof.
move=> mfA.
have [Ax|nAx] := pselect (forall a, (A `\ x) a -> f a != f x).
  by rewrite image_setD1//; apply: measurableD.
by rewrite not_image_setD1.
Qed.

Let measure0_image_setI_set1 (f : R -> R) (A : set R) (x : R) :
  mu (f @` (A `&` [set x])) = 0.
Proof.
rewrite setI1; case: ifP; rewrite ?image_set0// image_set1 => _.
exact: lebesgue_measure_set1.
Qed.

Let measure0_setI_set1 (A : set R) (x : R) :
  mu (A `&` [set x]) = 0.
Proof.
rewrite setI1; case: ifP => //.
by rewrite lebesgue_measure_set1.
Qed.

(* generalize? *)
Let measure_image_setD_set1 (f : R -> R) (A : set R) (x : R) :
  mu (f @` (A `\ x)) = mu (f @` A).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: le_outer_measure.
  rewrite setDE.
  apply: (subset_trans sub_image_setI).
  exact: subIsetl.
rewrite -{1}(setUIDK A [set x]).
rewrite image_setU.
apply: (le_trans (outer_measureU2 _ _ _)) => /=.
have := measure0_image_setI_set1 f A x.
rewrite /lebesgue_measure/lebesgue_stieltjes_measure/measure_extension.
by move->; rewrite add0r.
Qed.

(* testing strict increasing version *)
Lemma image_measure0_Lusin_increasing (F : R -> R) :
  {within `[a, b], continuous F} ->
  {in `[a, b] &, {homo F : x y / x < y}} ->
  (forall Z : set R, Z `<=` `[a, b]%classic ->
      compact Z ->
      mu Z = 0 ->
      mu (F @` Z) = 0) ->
  lusinN `[a, b] F.
Proof.
move=> cF incF lusinN'.
apply: contrapT.
move=> /existsNP[Z]/not_implyP[Zab/=] /not_implyP[mZ] /not_implyP[muZ0].
move=> /eqP; rewrite neq_lt ltNge measure_ge0/= => muFZ0.
have Zoo : (mu Z < +oo)%E.
  apply: (@le_lt_trans _ _ (mu `[a, b])); first exact: le_outer_measure.
  by rewrite lebesgue_measure_itv/= lte_fin ab -EFinD ltry.
have [U_ [U0oo ZU oU _ mZIU]] := lebesgue_measure_Gdelta_approx Zoo.
set Z1 := `]a, b[ `&` \bigcap_n U_ n.
have muZ10 : mu Z1 = 0.
  apply/eqP; rewrite -measure_le0/= -muZ0.
  rewrite completed_lebesgue_measureE.
  rewrite /lebesgue_measure/lebesgue_stieltjes_measure/measure_extension mZIU.
  apply: le_outer_measure.
  exact: subIsetr.
have Z1ab : Z1 `<=` `]a, b[ by exact: subIsetl.
have Z1oo : (mu (F @` Z1) < +oo)%E.
  apply: (@le_lt_trans _ _ (mu (F @` `[a, b]))).
    apply: le_outer_measure.
    apply: image_subset.
    apply: (subset_trans Z1ab).
    exact: subset_itv_oo_cc.
  rewrite continuous_increasing_image_itv//.
  rewrite lebesgue_measure_itv lte_fin incF// -?EFinB ?ltry//.
    by rewrite boundl_in_itv/= bnd_simp ltW.
  by rewrite boundr_in_itv bnd_simp ltW.
have gZ1 : Gdelta Z1.
  apply: GdeltaIr => //.
  by exists U_.
(* using lemma2 *)
have mFZ1 : measurable (F @` Z1).
apply: measurable_image_Gdelta_set_nondecreasing_fun Z1ab gZ1 => //.
  by move=> ? ? ? ?; rewrite le_eqVlt => /predU1P[->//|xy]; exact/ltW/incF.
have ZZ1 : Z `\ a `\ b `<=` Z1.
  rewrite subsetI; split.
  - rewrite -(setIidr Zab).
    rewrite -(setU1itv false) ?bnd_simp ?ltW//.
    rewrite setIUl setDUl.
    rewrite setIC -setIDA setDv setI0 set0U.
    rewrite -(setUitv1 true) ?bnd_simp ?ltW//.
    rewrite setIUl 2!setDUl -2!setIDA.
    rewrite -setIDA (setIC [set b]) -setIDA setDv setI0 setU0.
    exact: subIsetl.
  - apply: sub_bigcap => n _.
    apply: subset_trans (ZU n).
    rewrite setDDl.
    exact: subDsetl.
have FZ1oo : (mu (F @` Z1) < +oo)%E.
  apply: (@le_lt_trans _ _ (mu (F @` `]a, b[))).
    apply: le_outer_measure.
    exact: image_subset.
  apply: (@le_lt_trans _ _ (mu `[F a, F b])).
    apply: le_outer_measure.
    rewrite -continuous_increasing_image_itv => //.
    apply: image_subset.
    exact: subset_itv_oo_cc.
  rewrite lebesgue_measure_itv.
  by case: ifP=> //; rewrite -EFinB ltry.
have FZ10 : (0 < mu (F @` Z1))%E.
  apply: (@lt_le_trans _ _ (mu (F @` (Z `\ a `\ b)))).
    by rewrite 2!measure_image_setD_set1.
  apply: le_outer_measure.
  exact: image_subset.
set e := fine (mu (F @` Z1)) / 2.
have e0 : 0 < e by rewrite divr_gt0 ?fine_gt0 ?FZ1oo ?FZ10.
have [K [cK KFZ1 Z1Ke]] := lebesgue_regularity_inner mFZ1 FZ1oo e0.
set K1 := `[a, b] `&` F @^-1` K.
have K1K : F @` K1 = K.
  rewrite eqEsubset; split.
    apply: (subset_trans sub_image_setI).
    apply: subIset; right.
    exact: image_preimage_subset.
  move=> r Kr/=.
  pose L := `[a, b] `&` preimage F [set r].
  have L0 : L !=set0.
    have [] := @IVT _ _ _ _ r (ltW ab) cF.
      have Fab : F a < F b.
        apply: incF => //.
        - by rewrite boundl_in_itv bnd_simp ltW.
        - by rewrite boundr_in_itv bnd_simp ltW.
      rewrite minElt Fab.
      rewrite maxElt Fab.
      move: Kr => /KFZ1[t [/= tab _] <-].
      rewrite 2?ltW ?incF//.
      - by rewrite bound_itvE// ltW.
      - exact: subset_itv_oo_cc.
      - by move: tab; rewrite in_itv/= => /andP[].
      - exact: subset_itv_oo_cc.
      - by rewrite bound_itvE// ltW.
      - by move: tab; rewrite in_itv/= => /andP[].
    by move=> x xab; rewrite /L; move <-; exists x.
  move: (L0) => [r'] /[dup] Lr'.
  rewrite /L/= => [[r'ab Fr'r]].
  exists r' => //.
  rewrite /K1/=; split => //.
  by rewrite Fr'r.
have : (0 < mu (F @` K1))%E.
  rewrite K1K.
  have := Z1Ke.
  rewrite measureD//; first exact: compact_measurable.
  rewrite setIidr//.
  rewrite lteBlDl.
    rewrite ge0_fin_numE//.
    apply: le_lt_trans FZ1oo.
    exact: le_outer_measure.
  rewrite -lteBlDr//.
  apply: le_lt_trans.
  rewrite sube_ge0// /e EFinM fineK; first by rewrite ge0_fin_numE.
  rewrite muleC gee_pMl//.
  rewrite lee_fin invf_le1//.
  by rewrite -[leLHS](mulr1n 1) ler_nat.
apply/negP.
rewrite -leNgt.
rewrite measure_le0/=.
apply/eqP.
apply: lusinN'.
- exact: subIsetl.
- rewrite /K1 setIC.
  rewrite -(setIid `[a, b]%classic) setICA.
  apply: compact_closedI => //; first exact: segment_compact.
  rewrite closed_setIS; first exact: interval_closed.
  apply: (continuous_closedP _).1 => //.
  exact: compact_closed.
- apply/eqP; rewrite -measure_le0/= -muZ10.
  have bijF := continuous_increasing_set_bij ab cF incF.
  have [F' FF'] := pPbij bijF.
  rewrite /K1 FF' -inv_sub_image.
    apply: (subset_trans KFZ1).
    rewrite -continuous_increasing_image_itv//.
    apply: image_subset.
    apply: (subset_trans Z1ab).
    exact: subset_itv_oo_cc.
  apply: le_outer_measure.
  rewrite image_sub.
  apply: subset_trans (@inv_image_sub _ _ _ _ _ Z1 _) => /=; last first.
    apply: (subset_trans Z1ab).
    exact: subset_itv_oo_cc.
  rewrite invV.
  by move=> ? ?/=; rewrite -FF'; exact: KFZ1.
Abort.

  (* Lemma open_subset_itvoocc S : open S -> S `<=` `[a, b] -> S `<=` `]a, b[. *)
  (*   move=> oS Sab. *)
  (*   apply: (@subset_trans _ [set` Rhull S]). *)
  (*     exact: sub_Rhull. *)
  (*     (* lemma? *) *)
  (*   have itv_closure_subset : {in (@is_interval R) : set (set R) &, {mono closure : i j / i `<=` j}}. *)
  (*     move=> i j itvi itvj. *)
  (*     rewrite propeqE; split. *)
  (*       admit. *)
  (*     exact: closure_subset. *)
  (*   rewrite -itv_closure_subset; last 2 first. *)
  (*       admit. *)
  (*     admit. *)
  (*   rewrite closure_itvoo //. *)
  (*   (* lemma? *) *)
  (*   have closurer_subset X (x y : R) : X `<=` `[x, y] -> closure X `<=` `[x, y]. *)
  (*     admit. *)
  (*   apply: closurer_subset. *)
  (*   (* lemma? *) *)
  (*   have sub_Rhullr (i : interval R) : S `<=` [set` i] -> [set` Rhull S] `<=` [set` i]. *)
  (*     admit. *)
  (*   by apply: sub_Rhullr. *)


(* NB: available as PR https://github.com/math-comp/analysis/pull/1809 *)
Lemma compact_unif_continuousP f :
  {within `[a, b], continuous f} <-> @unif_continuous (subspace `[a, b]) R f.
Proof.
Admitted.

Section main_lemma.

(* NB: this is too long! *)
Lemma nondecreasing_cont_isolated (F : R -> R) (K : set R) :
  compact K ->
  {within `[a, b], continuous F} ->
  {in `[a, b] &, {homo F : x y / x <= y}} ->
  isolated K = set0 ->
  let A := `[a, b] `&` F @^-1` K : set R in
  [set F x | x in A] = K ->
  isolated A = set0.
Proof.
move=> cK cF ndF isoK0 A AK.
apply/nonemptyPn => -[/= x].
move/isolatedP => [/=].
rewrite inE => -[/= xab].
set y := F x.
move=> KFx.
have : limit_point K y.
  have : (closure K) y by exact: subset_closure.
  by rewrite closure_isolated_limit_point isoK0 set0U.
move/limit_pointP => [y_ [y_K y_neq y_cvg]].
move=> -[V + VAx].
move/open_nbhs_nbhs.
rewrite /nbhs/= /nbhs_ball_ => -[d /= d0 xdV].
have [xa|[xb|{}xab]] : x = a \/ x = b \/ x \in `]a, b[.
  have : x \in `[a, b]%classic.
    by rewrite inE.
  rewrite -(setU1itv false) ?bnd_simp//; first exact/ltW.
  rewrite -(setUitv1 true) ?bnd_simp//.
  by rewrite setUA setUAC inE/= orA.
- subst x.
  pose d' := Num.min (d / 2) (b - a).
  have d'0 : 0 < d'.
    by rewrite /d' lt_min divr_gt0// subr_gt0.
  have : F a <= F (a + d').
    rewrite ndF//.
      rewrite in_itv/=; apply/andP; split.
        by rewrite lerDl ltW.
      by rewrite -lerBrDl ge_min lexx orbT.
    by rewrite lerDl ltW.
  rewrite le_eqVlt => /predU1P[FaFad'|FaFad'].
    have : (V `&` A) (a + d').
      split.
        apply: xdV.
        rewrite /ball_/=.
        rewrite opprD addrA subrr add0r normrN gtr0_norm//.
        by rewrite gt_min gtr_pMr// invf_lt1// ltr1n.
      rewrite /A/=; split.
        rewrite in_itv/= lerDl ltW//=.
        by rewrite -lerBrDl ge_min lexx orbT.
      rewrite -FaFad' -AK/=.
      by exists a => //.
    rewrite VAx/=.
    apply/eqP.
    by rewrite eq_sym lt_eqF// ltrDl.
  have [n /andP[Fayn ynFad']] : exists n, F a < y_ n < F (a + d').
    pose k := ((F (a + d') - F a) / 2).
    have k0 : 0 < k.
      by rewrite divr_gt0// subr_gt0.
    move/cvgrPdist_lt : y_cvg => /(_ _ k0)[n _]/(_ n (@leqnn n)).
    rewrite ltr_distlC => /andP[ykyn ynyk].
    exists n.
    apply/andP; split.
      rewrite lt_neqAle; apply/andP; split.
        by rewrite eq_sym y_neq.
      have := y_K (y_ n).
      move=> /(_ (imageT _ _)).
      rewrite -AK/= => -[x' Ax' <-].
      rewrite ndF//.
        move: Ax'.
        by rewrite /A/= => -[].
      move: Ax'.
      by rewrite /A/= => -[] /itvP ->.
    rewrite (lt_le_trans ynyk)//.
    rewrite -lerBrDl.
    rewrite /k -/y.
    rewrite ger_pMr.
      by rewrite subr_gt0.
    by rewrite invf_le1// ler1n//.
  have H3 : {within `[a, a + d'], continuous F}.
    apply: continuous_subspaceW cF.
    apply: subset_itv; rewrite bnd_simp//=.
    by rewrite -lerBrDl ge_min lexx orbT.
  have : Num.min (F a) (F (a + d')) <= y_ n <=
         Num.max (F a) (F (a + d')).
    by rewrite ge_min (ltW Fayn)/= le_max (ltW ynFad') orbT.
  have aad' : a <= a + d'.
    by rewrite lerDl ltW.
  move/IVT => /(_ aad' H3)[x' x'aad' Fx'yn].
  have : x' \in V `&` A.
    rewrite inE.
    split.
      apply: xdV.
      apply/set_mem.
      rewrite -[X in _ \in X]/(ball _ _).
      rewrite ball_itv inE/=.
      apply: subset_itv x'aad'; rewrite bnd_simp//=.
        by rewrite ltrBlDl ltrDr.
      by rewrite ltrD2l gt_min gtr_pMr// invf_lt1//= ltr1n.
    rewrite /A; split => //=.
      apply: subset_itvl x'aad'; rewrite bnd_simp -lerBrDl.
      by rewrite ge_min lexx orbT.
    rewrite Fx'yn.
    apply/y_K.
    by apply/imageT.
  rewrite VAx inE/= => x'x.
  subst x'.
  move/eqP : Fx'yn.
  apply/negP.
  rewrite eq_sym.
  exact: y_neq.
- subst x.
  pose d' := Num.min (d / 2) (b - a).
  have d'0 : 0 < d'.
    by rewrite /d' lt_min divr_gt0// subr_gt0.
  have : F (b - d') <= F b.
    rewrite ndF//.
      rewrite in_itv/=; apply/andP; split.
        by rewrite lerBrDl -lerBrDr ge_min lexx orbT.
      by rewrite lerBlDl lerDr// ltW.
     by rewrite lerBlDl lerDr// ltW.
  rewrite le_eqVlt => /predU1P[FbFbd'|FbFbd'].
    have : (V `&` A) (b - d').
      split.
        apply: xdV.
        rewrite /ball_/=.
        rewrite opprD addrA opprK subrr add0r gtr0_norm//.
        by rewrite gt_min gtr_pMr// invf_lt1// ltr1n.
      rewrite /A/=; split.
        rewrite in_itv/= lerBlDl lerDr (ltW d'0) andbT.
        by rewrite lerBrDr -lerBrDl ge_min lexx orbT.
      rewrite FbFbd' -AK/=.
      by exists b => //.
    rewrite VAx/=.
    apply/eqP.
    by rewrite eq_sym gt_eqF// ltrBlDl ltrDr.
  have [n /andP[Fbyn ynFbd']] : exists n, F (b - d') < y_ n < F b.
    pose k := ((F b - F (b - d')) / 2).
    have k0 : 0 < k by rewrite divr_gt0// subr_gt0.
    move/cvgrPdist_lt : y_cvg => /(_ _ k0)[n _]/(_ n (@leqnn n)).
    rewrite ltr_distlC => /andP[ykyn ynyk].
    exists n.
    apply/andP; split.
      rewrite (le_lt_trans _ ykyn)//.
      rewrite lerBrDr -lerBrDl /y.
      rewrite /k.
      rewrite ger_pMr.
        by rewrite subr_gt0.
      by rewrite invf_le1// ler1n//.
    rewrite lt_neqAle; apply/andP; split.
      by rewrite y_neq.
    have := y_K (y_ n).
    move=> /(_ (imageT _ _)).
    rewrite -AK/= => -[x' Ax' <-].
    rewrite ndF//.
      move: Ax'.
      by rewrite /A/= => -[].
    move: Ax'.
    by rewrite /A/= => -[] /itvP ->.
  have H3 : {within `[b - d', b], continuous F}.
    apply: continuous_subspaceW cF.
    apply: subset_itv; rewrite bnd_simp//=.
    by rewrite lerBrDl -lerBrDr ge_min lexx orbT.
  have : Num.min (F (b - d')) (F b) <= y_ n <=
         Num.max (F (b - d')) (F b).
    by rewrite ge_min (ltW Fbyn)/= le_max (ltW ynFbd') orbT.
  have bd'b : b - d' <= b.
    rewrite lerBlDl.
    by rewrite lerDr ltW.
  move/IVT => /(_ bd'b H3)[x' x'bd'b Fx'yn].
  have : x' \in V `&` A.
    rewrite inE.
    split.
      apply: xdV.
      apply/set_mem.
      rewrite -[X in _ \in X]/(ball _ _).
      rewrite ball_itv inE/=.
      apply: subset_itv x'bd'b; rewrite bnd_simp//=.
        by rewrite ltrD2l ltrN2 // gt_min gtr_pMr// invf_lt1//= ltr1n.
      by rewrite ltrDl.
    rewrite /A; split => //=.
      apply: subset_itvr x'bd'b; rewrite bnd_simp.
      rewrite lerBrDl -lerBrDr.
      by rewrite ge_min lexx orbT.
    rewrite Fx'yn.
    apply/y_K.
    by apply/imageT.
  rewrite VAx inE/= => x'x.
  subst x'.
  move/eqP : Fx'yn.
  apply/negP.
  rewrite eq_sym.
  exact: y_neq.
pose d' := Num.min (d/2) (Num.min (x - a) (b - x)).
have d'0 : 0 < d'.
  by rewrite lt_min divr_gt0//= lt_min !subr_gt0 !(itvP xab).
have axd' : a <= x - d'.
  by rewrite lerBrDl -lerBrDr !ge_min lexx/= orbT.
have xd'b : x + d' <= b.
  by rewrite -lerBrDl !ge_min lexx/= !orbT.
have xd'xd' : x - d' <= x + d'.
  by rewrite lerBlDr -addrA lerDl addr_ge0// ltW.
have xd'ab : ball x d' `<=` `[a, b].
  move=> z.
  rewrite ball_itv/=.
  by apply: subset_itv; rewrite bnd_simp.
have : F (x - d') <= F (x + d').
  apply: ndF => //.
  rewrite in_itv/=; apply/andP; split => //.
    by rewrite (le_trans _ xd'b)//.
  rewrite in_itv/=; apply/andP; split => //.
  by rewrite (le_trans axd').
have d'd : d' < d.
  by rewrite !gt_min gtr_pMr// invf_lt1// ltr1n.
have xBd'b : x - d' <= b.
  rewrite lerBlDl -lerBlDr !le_min.
  rewrite lerD2l lerN2 (ltW ab)/=.
  apply/andP; split.
    rewrite lerBlDl -lerBlDr (le_trans _ xd'b)//.
    rewrite lerD2l (@le_trans _ _ 0)//.
      by rewrite lerNl oppr0 divr_ge0// ltW.
    by rewrite ltW.
  rewrite lerBlDl addrA -lerBlDr opprK.
  by rewrite lerD// (itvP xab).
have axDd' : a <= x + d'.
  rewrite -lerBlDl !le_min.
  rewrite lerD2r (ltW ab) andbT.
  apply/andP; split.
    rewrite lerBlDl (le_trans axd')// lerD2l (@le_trans _ _ 0)//.
      by rewrite lerNl oppr0 ltW.
    by rewrite divr_ge0// ltW.
  rewrite lerBlDl addrA -lerBlDr opprK.
  by rewrite lerD// (itvP xab).
rewrite le_eqVlt => /predU1P[FxBd|FxBd].
  have {}FxBd : F x = F (x + d').
    apply/eqP/negPn/negP; rewrite neq_lt => /orP[|].
      rewrite -FxBd ltNge => /negP; apply.
      rewrite ndF ?in_itv//=.
      by rewrite axd' xBd'b.
      by rewrite !(itvP xab).
      by rewrite gerBl ltW.
    rewrite ltNge => /negP; apply.
    rewrite ndF ?in_itv//=.
    by rewrite !(itvP xab).
    by rewrite xd'b andbT axDd'.
    by rewrite lerDl// ltW.
  have : (V `&` A) (x + d').
    split.
      apply: xdV.
      rewrite /ball_/=.
      by rewrite opprD addrA subrr add0r normrN gtr0_norm//.
    rewrite /A/=; split.
      rewrite in_itv/= xd'b andbT.
      by rewrite (ler_wpDr (ltW _))// (itvP xab).
    by rewrite -FxBd.
  rewrite VAx/=.
  by apply/eqP; rewrite eq_sym lt_eqF// ltrDl.
have [yE|Fxd'y] := eqVneq (F (x - d')) y.
  have : (V `&` A) (x - d').
    split.
      apply: xdV.
      rewrite /ball_/= opprD addrA subrr add0r normrN ltr0_norm//.
      - by rewrite oppr_lt0.
      - by rewrite opprK.
    rewrite /A/=; split.
      by rewrite in_itv/= axd'.
    by rewrite yE.
  rewrite VAx/=.
  by apply/eqP; rewrite eq_sym gt_eqF// ltrBlDl ltrDr.
have [yE|] := eqVneq (F (x + d')) y.
  have : (V `&` A) (x + d').
    split.
      apply: xdV.
      by rewrite /ball_/= opprD addrA subrr add0r normrN gtr0_norm.
    rewrite /A/=; split.
      by rewrite in_itv/= xd'b andbT (le_trans axd').
    by rewrite yE.
  rewrite VAx/=.
  by apply/eqP; rewrite eq_sym lt_eqF// ltrDl.
move=> yFxd'.
have [n /andP[xd'yn ynxd']] : exists n, F (x - d') < y_ n < F (x + d').
  pose k := Num.min ((F (x + d') - y) / 2) ((y - F (x - d')) / 2).
  have k0 : 0 < k.
    rewrite lt_min !divr_gt0//.
      rewrite subr_gt0 lt_neqAle eq_sym yFxd'/= ndF//.
      - exact: subset_itv_oo_cc.
      - by rewrite in_itv/= axDd'.
      - by rewrite lerDl ltW.
    rewrite subr_gt0 lt_neqAle Fxd'y ndF//.
    - by rewrite in_itv/= axd'//= (le_trans _ xd'b)//.
    - exact: subset_itv_oo_cc.
    - by rewrite lerBlDl lerDr ltW.
  move/cvgrPdist_lt : y_cvg => /(_ _ k0)[n _]/(_ n (@leqnn n)).
  rewrite ltr_distlC => /andP[ykyn ynyk].
  exists n; apply/andP; split.
    rewrite (le_lt_trans _ ykyn)// /k lerBrDl -lerBrDr ge_min.
    apply/orP; right.
    rewrite ler_piMr//; last by rewrite ?invf_le1 ?ler1n//.
    rewrite subr_ge0 ndF//.
    - by rewrite in_itv/= axd'/= (le_trans xd'xd').
    - by rewrite in_itv/= !(itvP xab).
    - by rewrite lerBlDl lerDr ltW.
  rewrite (lt_le_trans ynyk)// /k -lerBrDl ge_min.
  apply/orP; left.
  rewrite ler_piMr//; last by rewrite ?invf_le1 ?ler1n//.
  rewrite subr_ge0 ndF//.
  - by rewrite in_itv/= !(itvP xab).
  - rewrite in_itv/= xd'b andbT.
    by rewrite (le_trans axd')//.
  - by rewrite lerDl ltW.
have xd'F : {within `[x - d', x + d'], continuous F}.
  apply: continuous_subspaceW cF.
  by apply: subset_itv; rewrite bnd_simp.
have : Num.min (F (x - d')) (F (x + d')) <= y_ n <=
       Num.max (F (x - d')) (F (x + d')).
  by rewrite ge_min (ltW xd'yn)/= le_max (ltW ynxd') orbT.
move/IVT => /(_ xd'xd' xd'F)[x' x'xd Fx'yn].
have : x' \in V `&` A.
  rewrite inE; split.
    apply/xdV/set_mem.
    rewrite -[X in _ \in X]/(ball _ _) ball_itv inE/=.
    apply: subset_itv x'xd; rewrite bnd_simp//=.
      by rewrite ltrD2l ltrN2.
    by rewrite ltrD2l.
  rewrite /A; split => /=.
    by apply: subset_itv x'xd; rewrite bnd_simp.
  rewrite Fx'yn.
  exact/y_K/imageT.
rewrite VAx inE/= => x'x.
move: Fx'yn x'xd; rewrite x'x {x'x x'}.
move=> /eqP /[swap] x'xd; apply/negP.
by rewrite eq_sym y_neq.
Qed.

Arguments open : clear implicits.
Arguments closed : clear implicits.
Arguments compact : clear implicits.
Arguments continuous_at : clear implicits.

(* lemma3 (converse) *)
(* NB: 1. In Hypothesis, "F is increasing" means nondecreasing or not?        *)
(*     2. In wlog step, "Gdelta-type" means Gdelta set?                       *)
(*        Then, can we obtain Z1 as (closure Z)?                              *)
(*     3. In Hypothesis and proof, when Gdelta-type doesn't means Gdelta set, *)
(*        "compact" means precompact, as compactness in `[a, b]?              *)

#[deprecated(note="use the more general version instead")]
Lemma image_measure0_Lusin_nondecreasing (F : R -> R) :
  {within `[a, b], continuous F} ->
  (* increasing means nondecreasing or not? *)
  {in `[a, b] &, {homo F : x y / x <= y}} ->
  (forall Z : set R, Z `<=` `[a, b]%classic ->
      compact R Z ->
      mu Z = 0 ->
      mu (F @` Z) = 0) ->
  lusinN `[a, b] F.
Proof.
move=> cF ndF HZ.
(* Suppose on the contrary that F \notin (N) on `[a, b] *)
apply: contrapT.
(*Then there exists ... *)
move=> /existsNP[Z]/not_implyP[Zab/=] /not_implyP[mZ] /not_implyP[muZ0].
move=> /eqP; rewrite neq_lt ltNge measure_ge0/= => muFZ0.
have Zoo : (mu Z < +oo)%E.
  apply: (@le_lt_trans _ _ (mu `[a, b])); first exact: le_outer_measure.
  by rewrite lebesgue_measure_itv/= lte_fin ab -EFinD ltry.
(* wlog (we should read Z1 as Z in paper) *)
have [U_ [U0oo ZU oU _ mZIU]] := lebesgue_measure_Gdelta_approx Zoo.
set Z1 := `]a, b[ `&` \bigcap_n U_ n.
have muZ10 : mu Z1 = 0.
  apply/eqP; rewrite -measure_le0/= -muZ0.
  rewrite completed_lebesgue_measureE.
  rewrite /lebesgue_measure/lebesgue_stieltjes_measure/measure_extension mZIU.
  apply: le_outer_measure.
  exact: subIsetr.
have gZ1 : Gdelta Z1.
 exists (fun n => `]a, b[ `&` U_ n).
    by move=> n; apply: openI.
  by rewrite bigcapIr.
have Z1ab : Z1 `<=` `]a, b[ by exact: subIsetl.
have mFZ1 : measurable (F @` Z1).
  exact: measurable_image_Gdelta_set_nondecreasing_fun Z1ab gZ1.
have FZ1oo : (mu (F @` Z1) < +oo)%E.
  apply: (@le_lt_trans _ _ (mu (F @` `]a, b[))).
    apply: le_outer_measure.
    exact: image_subset.
  apply: (@le_lt_trans _ _ (mu `[F a, F b])).
    apply: le_outer_measure.
    apply: continuous_nondecreasing_image_itvoo => //.
    by move=> ? ? ? ?; apply: ndF; exact: subset_itv_oo_cc.
  rewrite lebesgue_measure_itv.
  by case: ifP => //; rewrite -EFinB ltry.
have ZabZ1 : Z `\ a `\ b `<=` Z1.
  rewrite subsetI; split.
  - rewrite -(setIidr Zab).
    rewrite -(setU1itv false) ?bnd_simp ?ltW//.
    rewrite setIUl setDUl.
    rewrite setIC -setIDA setDv setI0 set0U.
    rewrite -(setUitv1 true) ?bnd_simp ?ltW//.
    rewrite setIUl 2!setDUl -2!setIDA.
    rewrite -setIDA (setIC [set b]) -setIDA setDv setI0 setU0.
    exact: subIsetl.
  - apply: sub_bigcap => n _.
    apply: subset_trans (ZU n).
    rewrite setDDl.
    exact: subDsetl.
have FZ10 : (0 < mu (F @` Z1))%E.
  apply: (@lt_le_trans _ _ (mu (F @` (Z `\ a `\ b)))).
    by rewrite 2!measure_image_setD_set1.
  apply: le_outer_measure.
  exact: image_subset.
set e := fine (mu (F @` Z1)) / 2.
have e0 : 0 < e by rewrite divr_gt0 ?fine_gt0 ?FZ1oo ?FZ10.
set FZ1' := ((F @` Z1) `\` preimages_gt1 `[a, b] [set: R] F).
set e' := fine (mu FZ1') / 2.
have mpreF0 : mu ([set F x | x in Z1] `&` preimages_gt1 `[a, b] [set: R] F) = 0.
  apply: countable_lebesgue_measure0.
  apply: (@sub_countable _ _ _ (preimages_gt1 `[a, b] [set: R] F)).
    apply: subset_card_le.
    exact: subIsetr.
  exact: is_countable_preimages_gt1_nondecreasing_fun.
have e'0 : 0 < e'.
  rewrite /e' measureD//=.
    apply: countable_measurable => //.
    exact: is_countable_preimages_gt1_nondecreasing_fun.
  rewrite mpreF0 sube0.
  exact: e0.
have FZ1'oo : (mu FZ1' < +oo)%E.
  apply: le_lt_trans FZ1oo.
  apply: le_outer_measure.
  exact: subIsetl.
have mFZ1' : measurable FZ1'.
  apply: measurableI => //.
  apply: measurableC.
  apply: countable_measurable => //.
  exact: is_countable_preimages_gt1_nondecreasing_fun.
have [K [cK KFZ1' FZ1'Ke']] := lebesgue_regularity_inner mFZ1' FZ1'oo e'0.
set K1 := `[a, b] `&` F @^-1` K.
have K1K : F @` K1 = K.
  rewrite eqEsubset; split.
    apply: (subset_trans sub_image_setI).
    apply: subIset; right.
    exact: image_preimage_subset.
  move=> r Kr/=.
  pose L := `[a, b] `&` preimage F [set r].
  have L0 : L !=set0.
    have [] := @IVT _ _ _ _ r (ltW ab) cF.
      have Fab : F a <= F b.
        apply: ndF => //.
        - by rewrite boundl_in_itv bnd_simp ltW.
        - by rewrite boundr_in_itv bnd_simp ltW.
        - exact: ltW.
      rewrite minEle Fab.
      rewrite maxEle Fab.
      move: Kr=> /KFZ1'.
      case=> -[t [/= tab _] <-] _.
      rewrite 2?ndF//.
      - by rewrite bound_itvE// ltW.
      - exact: subset_itv_oo_cc.
      - by apply/ltW; move: tab; rewrite in_itv/= => /andP[].
      - exact: subset_itv_oo_cc.
      - by rewrite bound_itvE// ltW.
      - by apply/ltW; move: tab; rewrite in_itv/= => /andP[].
    by move=> x xab; rewrite /L; move <-; exists x.
  move: (L0) => [r'] /[dup] Lr'.
  rewrite /L/= => [[r'ab Fr'r]].
  exists r' => //.
  rewrite /K1/=; split => //.
  by rewrite Fr'r.
have : (0 < mu (F @` K1))%E.
  rewrite K1K.
  have := FZ1'Ke'.
  rewrite measureD//; first exact: compact_measurable.
  rewrite setIidr//.
  rewrite lteBlDl.
    rewrite ge0_fin_numE//.
    apply: le_lt_trans FZ1'oo.
    exact: le_outer_measure.
  rewrite -lteBlDr//.
  apply: le_lt_trans.
  rewrite sube_ge0// /e EFinM fineK; first by rewrite ge0_fin_numE.
  rewrite muleC gee_pMl//.
  rewrite lee_fin invf_le1//.
  by rewrite -[leLHS](mulr1n 1) ler_nat.
apply/negP.
rewrite -leNgt.
rewrite measure_le0/=.
apply/eqP.
apply: HZ.
- exact: subIsetl.
- rewrite /K1 setIC -(setIid `[a, b]%classic) setICA.
  apply: compact_closedI; first exact: segment_compact.
  rewrite closed_setIS; first exact: itv_closed.
  apply: ((@continuous_closedP (subspace `[a, b]) _ F).1 cF).
  exact: compact_closed cK.
- apply/eqP; rewrite -measure_le0/=.
  rewrite -muZ10.
  apply: le_outer_measure.
  apply: (@subset_trans _ (`[a, b] `&` F @^-1` FZ1')).
    apply: setIS.
    exact: preimage_subset.
  rewrite /FZ1' setDE.
  rewrite [X in X `<=` _](_: _
    = Z1 `\` (F @^-1` preimages_gt1 `[a, b] [set: R] F)).
    rewrite eqEsubset; split.
    - move=> x/= [xab [[x' Z1x' Fx'Fx ]]].
      (* lemma? *)
      rewrite /preimages_gt1.
      rewrite not_andE not_notE orNp => /(_ Logic.I) sub1Fx.
      split => //.
      rewrite (sub1Fx x x')//.
      split => //.
      rewrite /=.
      apply: subset_itv_oo_cc.
      exact: Z1ab.
    - move=> x/= [Z1x].
      (* lemma? *)
      rewrite /preimages_gt1.
      rewrite not_andE not_notE orNp => /(_ Logic.I) sub1Fx.
      split => //.
        apply: subset_itv_oo_cc.
        exact: Z1ab.
      split => //.
      by exists x.
  exact: subDsetl.
Qed.

Lemma image_measure0_Lusin_nondecreasing_isolated0 (F : R -> R) :
  {within `[a, b], continuous F} ->
  {in `[a, b] &, {homo F : x y / x <= y}} ->
  (forall Z : set R, Z `<=` `[a, b]%classic ->
      compact R Z ->
      isolated Z = set0 (* TODO: change compact to perfect set instead *) ->
      mu Z = 0 ->
      mu (F @` Z) = 0) ->
  lusinN `[a, b] F.
Proof.
move=> cF ndF HZ.
(* Suppose on the contrary that F \notin (N) on `[a, b] *)
apply: contrapT.
(*Then there exists ... *)
move=> /existsNP[Z]/not_implyP[Zab/=] /not_implyP[mZ] /not_implyP[muZ0].
move=> /eqP; rewrite neq_lt ltNge measure_ge0/= => muFZ0.
have Zoo : (mu Z < +oo)%E.
  apply: (@le_lt_trans _ _ (mu `[a, b])); first exact: le_outer_measure.
  by rewrite lebesgue_measure_itv/= lte_fin ab -EFinD ltry.
(* wlog (we should read Z1 as Z in paper) *)
have [U_ [U0oo ZU oU _ mZIU]] := lebesgue_measure_Gdelta_approx Zoo.
set Z1 := `]a, b[ `&` \bigcap_n U_ n.
have muZ10 : mu Z1 = 0.
  apply/eqP; rewrite -measure_le0/= -muZ0.
  rewrite completed_lebesgue_measureE.
  rewrite /lebesgue_measure/lebesgue_stieltjes_measure/measure_extension mZIU.
  apply: le_outer_measure.
  exact: subIsetr.
have gZ1 : Gdelta Z1.
 exists (fun n => `]a, b[ `&` U_ n).
    by move=> n; apply: openI.
  by rewrite bigcapIr.
have Z1ab : Z1 `<=` `]a, b[ by exact: subIsetl.
have mFZ1 : measurable (F @` Z1).
  exact: measurable_image_Gdelta_set_nondecreasing_fun Z1ab gZ1.
have FZ1oo : (mu (F @` Z1) < +oo)%E.
  apply: (@le_lt_trans _ _ (mu (F @` `]a, b[))).
    apply: le_outer_measure.
    exact: image_subset.
  apply: (@le_lt_trans _ _ (mu `[F a, F b])).
    apply: le_outer_measure.
    apply: continuous_nondecreasing_image_itvoo => //.
    by move=> ? ? ? ?; apply: ndF; exact: subset_itv_oo_cc.
  rewrite lebesgue_measure_itv.
  by case: ifP => //; rewrite -EFinB ltry.
have ZabZ1 : Z `\ a `\ b `<=` Z1.
  rewrite subsetI; split.
  - rewrite -(setIidr Zab).
    rewrite -(setU1itv false) ?bnd_simp ?ltW//.
    rewrite setIUl setDUl.
    rewrite setIC -setIDA setDv setI0 set0U.
    rewrite -(setUitv1 true) ?bnd_simp ?ltW//.
    rewrite setIUl 2!setDUl -2!setIDA.
    rewrite -setIDA (setIC [set b]) -setIDA setDv setI0 setU0.
    exact: subIsetl.
  - apply: sub_bigcap => n _.
    apply: subset_trans (ZU n).
    rewrite setDDl.
    exact: subDsetl.
have FZ10 : (0 < mu (F @` Z1))%E.
  apply: (@lt_le_trans _ _ (mu (F @` (Z `\ a `\ b)))).
    by rewrite 2!measure_image_setD_set1.
  apply: le_outer_measure.
  exact: image_subset.
set e := fine (mu (F @` Z1)) / 2.
have e0 : 0 < e by rewrite divr_gt0 ?fine_gt0 ?FZ1oo ?FZ10.
set FZ1' := ((F @` Z1) `\` preimages_gt1 `[a, b] [set: R] F).
set e' := fine (mu FZ1') / 2.
have mpreF0 : mu ([set F x | x in Z1] `&` preimages_gt1 `[a, b] [set: R] F) = 0.
  apply: countable_lebesgue_measure0.
  apply: (@sub_countable _ _ _ (preimages_gt1 `[a, b] [set: R] F)).
    apply: subset_card_le.
    exact: subIsetr.
  exact: is_countable_preimages_gt1_nondecreasing_fun.
have e'0 : 0 < e'.
  rewrite /e' measureD//=.
    apply: countable_measurable => //.
    exact: is_countable_preimages_gt1_nondecreasing_fun.
  rewrite mpreF0 sube0.
  exact: e0.
have FZ1'oo : (mu FZ1' < +oo)%E.
  apply: le_lt_trans FZ1oo.
  apply: le_outer_measure.
  exact: subIsetl.
have mFZ1' : measurable FZ1'.
  apply: measurableI => //.
  apply: measurableC.
  apply: countable_measurable => //.
  exact: is_countable_preimages_gt1_nondecreasing_fun.
have [K [cK KFZ1' FZ1'Ke']] := lebesgue_regularity_inner mFZ1' FZ1'oo e'0.
(* not in the original proof *)
wlog : K cK KFZ1' FZ1'Ke' / isolated K = set0.
  move=> wlg.
  have : (mu K < +oo)%E.
    rewrite (le_lt_trans _ FZ1'oo)//.
    by rewrite le_outer_measure.
  move/(perfect_set_rm cK) => [K0 [K0K cK0 isoK0 mK0]].
  apply: (wlg K0) => //.
  by apply: subset_trans KFZ1'.
  rewrite (le_lt_trans _ FZ1'Ke')//.
  rewrite measureD//.
    by apply: compact_measurable.
  rewrite [in leRHS]measureD//.
    by apply: compact_measurable.
  rewrite leeD//.
  rewrite leeN2.
  rewrite setIidr//.
  rewrite setIidr//.
    by apply: (subset_trans K0K).
  by rewrite [leRHS]mK0//.
(* / not in the original proof *)
move=> isoK0.
set K1 := `[a, b] `&` F @^-1` K.
have K1K : F @` K1 = K.
  rewrite eqEsubset; split.
    apply: (subset_trans sub_image_setI).
    apply: subIset; right.
    exact: image_preimage_subset.
  move=> r Kr/=.
  pose L := `[a, b] `&` preimage F [set r].
  have L0 : L !=set0.
    have [] := @IVT _ _ _ _ r (ltW ab) cF.
      have Fab : F a <= F b.
        apply: ndF => //.
        - by rewrite boundl_in_itv bnd_simp ltW.
        - by rewrite boundr_in_itv bnd_simp ltW.
        - exact: ltW.
      rewrite minEle Fab.
      rewrite maxEle Fab.
      move: Kr=> /KFZ1'.
      case=> -[t [/= tab _] <-] _.
      rewrite 2?ndF//.
      - by rewrite bound_itvE// ltW.
      - exact: subset_itv_oo_cc.
      - by apply/ltW; move: tab; rewrite in_itv/= => /andP[].
      - exact: subset_itv_oo_cc.
      - by rewrite bound_itvE// ltW.
      - by apply/ltW; move: tab; rewrite in_itv/= => /andP[].
    by move=> x xab; rewrite /L; move <-; exists x.
  move: (L0) => [r'] /[dup] Lr'.
  rewrite /L/= => [[r'ab Fr'r]].
  exists r' => //.
  rewrite /K1/=; split => //.
  by rewrite Fr'r.
have : (0 < mu (F @` K1))%E.
  rewrite K1K.
  have := FZ1'Ke'.
  rewrite measureD//; first exact: compact_measurable.
  rewrite setIidr//.
  rewrite lteBlDl.
    rewrite ge0_fin_numE//.
    apply: le_lt_trans FZ1'oo.
    exact: le_outer_measure.
  rewrite -lteBlDr//.
  apply: le_lt_trans.
  rewrite sube_ge0// /e EFinM fineK; first by rewrite ge0_fin_numE.
  rewrite muleC gee_pMl//.
  rewrite lee_fin invf_le1//.
  by rewrite -[leLHS](mulr1n 1) ler_nat.
apply/negP.
rewrite -leNgt.
rewrite measure_le0/=.
apply/eqP.
apply: HZ.
- exact: subIsetl.
- rewrite /K1 setIC -(setIid `[a, b]%classic) setICA.
  apply: compact_closedI; first exact: segment_compact.
  rewrite closed_setIS; first exact: itv_closed.
  apply: ((@continuous_closedP (subspace `[a, b]) _ F).1 cF).
  exact: compact_closed cK.
- (* not in the original proof *) exact: nondecreasing_cont_isolated.
- apply/eqP; rewrite -measure_le0/=.
  rewrite -muZ10.
  apply: le_outer_measure.
  apply: (@subset_trans _ (`[a, b] `&` F @^-1` FZ1')).
    apply: setIS.
    exact: preimage_subset.
  rewrite /FZ1' setDE.
  rewrite [X in X `<=` _](_: _
    = Z1 `\` (F @^-1` preimages_gt1 `[a, b] [set: R] F)).
    rewrite eqEsubset; split.
    - move=> x/= [xab [[x' Z1x' Fx'Fx ]]].
      (* lemma? *)
      rewrite /preimages_gt1.
      rewrite not_andE not_notE orNp => /(_ Logic.I) sub1Fx.
      split => //.
      rewrite (sub1Fx x x')//.
      split => //.
      rewrite /=.
      apply: subset_itv_oo_cc.
      exact: Z1ab.
    - move=> x/= [Z1x].
      (* lemma? *)
      rewrite /preimages_gt1.
      rewrite not_andE not_notE orNp => /(_ Logic.I) sub1Fx.
      split => //.
        apply: subset_itv_oo_cc.
        exact: Z1ab.
      split => //.
      by exists x.
  exact: subDsetl.
Qed.

End main_lemma.

End ene3.
