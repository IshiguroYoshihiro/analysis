From HB Require Import structures.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype.
From mathcomp Require Import sequences.
From mathcomp Require Import measure lebesgue_measure realfun.
From mathcomp Require Import absolute_continuity.
From mathcomp Require Import banach_zarecki_lemma2.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 7)                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition set01 {R : realType} (b : bool) (x : R) : set R :=
  if b then [set x] else set0.

Section measure_setU1.
Import MeasurableR.

Lemma measure_setU1 {R : realType} (a : R) (U : set R) :
  measurable U -> @lebesgue_measure R U = 0 ->
  @lebesgue_measure R (U `|` [set a]) = 0.
Proof.
move=> mU mU0.
have [aU|aU] := boolP (a \in U).
  by rewrite setUidl// => x ->; exact/set_mem.
rewrite measureU//=; last first.
  by rewrite mU0 lebesgue_measure_set1 adde0.
rewrite -subset0 => x [/=] /[swap] ->.
by move=> /mem_set; apply/negP.
Qed.

Lemma measure_bigsetU_set01 {R : realType} n (b : 'I_n -> bool) (x : 'I_n -> R) :
  @lebesgue_measure _ (\big[setU/set0]_(i < n) set01 (b i) (x i)) = 0.
Proof.
move: n b x; elim => [|n ih] b x.
  by rewrite big_ord0 measure0.
rewrite big_ord_recr//=; case: (b ord_max) => /=.
  rewrite measure_setU1//.
  apply: bigsetU_measurable => // i _.
  rewrite /set01.
  by case: ifPn => //.
by rewrite setU0.
Qed.

End measure_setU1.

Section Banach_Zarecki_lemma7.
Context {R : realType} (a b : R) (f : R -> R).
Hypothesis ab : a < b.

Local Notation mu := (@lebesgue_measure R).

Let set_fun_f : set_fun `[a, b]%classic [set: R] f.
Proof. by []. Qed.

HB.instance Definition _ := isFun.Build _ _ _ _ _ set_fun_f.

Let F : {fun `[a, b]%classic >-> [set: R]} := f.

Import MeasurableR.

(* lemma7 *)
Lemma Banach_Zarecki_nondecreasing :
  {within `[a, b], continuous f} ->
  {in `[a, b]  &, {homo f : x y / x <= y}} ->
  measurable_lusinN `[a, b] f ->
  abs_cont a b f.
Proof.
move=> cf nndf lf.
apply/abs_contP; apply: contrapT => /existsNP[e0] /forallNP fe0.
have {fe0} : forall d : {posnum R},
    exists n, exists B : nat -> R * R,
      [/\ (forall i, (i < n)%N -> (B i).1 < (B i).2 /\ `](B i).1, (B i).2[ `<=` `[a, b]),
          (forall i j : 'I_n, (i < j)%N -> (B i).2 <= (B j).1), (* NEW *)
          trivIset `I_n (fun i => `](B i).1, (B i).2[%classic),
          \sum_(k < n) ((B k).2 - (B k).1) < d%:num &
          \sum_(k < n) `|f (B k).2 - f (B k).1| >= e0%:num].
  move=> d; have {fe0} := fe0 d.
  move=> /existsNP[n] /existsNP[B] /not_implyP[] [H1 H2 H3 H4 H5].
  by exists n, B; split => //; rewrite leNgt; apply/negP.
move=> /choice[n_0 ab_0].
pose delta_0 (i : nat) : R := (2 ^+ i.+1)^-1.
have d_geo n : delta_0 n = geometric 2^-1 2^-1 n.
  by rewrite /geometric /= /delta_0 -exprVn exprS.
have d_geo0 : forall k, (0 < k)%N -> (delta_0 k.-1 = geometric 1 (2 ^-1) k).
  rewrite /geometric /= /delta_0 => t t0.
  by rewrite prednK// -exprVn mul1r.
have delta_0_ge0 (i : nat) : 0 < (2 ^+ i.+1)^-1 :> R by rewrite invr_gt0 exprn_gt0.
pose delta_ (i : nat) : {posnum R} := PosNum (delta_0_ge0 i).
pose n_ i := n_0 (delta_ i).
pose ab_ i := projT1 (cid (ab_0 (delta_ i))).
have ablt i t : (t < n_0 (delta_ i))%N -> (ab_ i t).1 < (ab_ i t).2.
  move=> tn0i.
  move: (projT2 (cid (ab_0 (delta_ i)))).
  move=> [] + _ _ _.
  by move=> /(_ _ tn0i)[+ _].
have absub i t : (t < n_ i)%N -> `](ab_ i t).1, (ab_ i t).2[ `<=` `[a, b].
  move=> tn.
  move: (projT2 (cid (ab_0 (delta_ i)))).
  move=> [+ _ _ _].
  by move/(_ t tn) => [_ +].
(* NEW *)
have ordered t : (forall i j : 'I_(n_ t), (i < j)%N -> (ab_ t i).2 <= (ab_ t j).1).
  move: (projT2 (cid (ab_0 (delta_ t)))).
  by case => _ + _ _ _ /=.
have tab_ t : trivIset `I_(n_ t)
    (fun i => `](ab_ t i).1, (ab_ t i).2[%classic).
  move: (projT2 (cid (ab_0 (delta_ t)))).
  by case => _ _ + _ _ /=.
have Hc n k : (k < n_ n)%N -> {within `[(ab_ n k).1, (ab_ n k).2], continuous f}.
  move=> knn.
  move: cf.
  apply: continuous_subspaceW.
  move=> /= x.
  rewrite !in_itv /=.
  move/andP => [].
  rewrite le_eqVlt.
  move/orP => [/eqP <- _|abnkx xabnk].
    have /= -> := incl_itv_lb (fun i=> (ablt n (nat_of_ord i) (ltn_ord i)))
      (fun i=> absub n (nat_of_ord i) (ltn_ord i)) (Ordinal knn).
    have /= := incl_itv_ub (fun i=> (ablt n (nat_of_ord i) (ltn_ord i)))
      (fun i=> absub n (nat_of_ord i) (ltn_ord i)) (Ordinal knn).
    apply: le_trans.
    exact/ltW/ablt.
  apply/andP; split.
    apply: (le_trans _ (ltW abnkx)).
    by have /= := (incl_itv_lb (fun i=> (ablt n (nat_of_ord i) (ltn_ord i)))
      (fun i=> absub n (nat_of_ord i) (ltn_ord i)) (Ordinal knn)).
  apply: (le_trans xabnk).
  by have /= := (incl_itv_ub (fun i=> (ablt n (nat_of_ord i) (ltn_ord i)))
      (fun i=> absub n (nat_of_ord i) (ltn_ord i)) (Ordinal knn)).
have Hhomo n k : (k < n_ n)%N -> {in `](ab_ n k).1, (ab_ n k).2[ &, {homo f : x y / x <= y}}.
  move=> knn x y xab yab.
  by apply: nndf; exact: (absub n k).
have d_prop i : \sum_(k < n_ i) (((ab_ i) k).2 - ((ab_ i) k).1) < delta_0 i.
  by rewrite /ab_; case: cid => ? [].
have e0_prop i : \sum_(k < n_ i) `|f (((ab_ i) k).2) - f ((ab_ i) k).1| >= e0%:num.
  by rewrite /ab_; case: cid => ? [].
have H3 i k : (k < n_0 (delta_ i))%N ->
    (ab_ i k).1 < (ab_ i k).2 /\ `](ab_ i k).1, (ab_ i k).2[ `<=` `[a, b].
  move=> in0i.
  rewrite /ab_; case: cid => ? [] /=.
  by move/(_ _ in0i).
pose E_ i : set R := \big[setU/set0]_(k < n_ i) `](ab_ i k).1, (ab_ i k).2[%classic.
have mE i : measurable (E_ i).
  apply: bigsetU_measurable => /=.
  by move=> k _.
pose G_ i := \bigcup_(j in [set j | (j >= i)%N]) E_ j.
have mG i : mu.-cara.-measurable (G_ i) by exact: bigcup_measurable.
pose A := \bigcap_i (G_ i).
have H2 : (@normr R _ 2^-1 < 1)%R by rewrite gtr0_norm// invf_lt1// ltr1n.
have H20 : 1 - 2^-1 != 0 :> R by rewrite lt0r_neq0// subr_gt0; apply: ltr_normlW.
have H1 : (@GRing.inv R 2) / (1 - 2^-1) = 1.
  by rewrite [X in X - _](splitr 1) div1r addrK divff.
have Eled n : (mu (E_ n) <= (delta_0 n)%:E)%E.
  rewrite measure_semi_additive_ord //=.
  - have := tab_ n.
    rewrite trivIset_mkcond/= => /trivIsetP/= tab_n.
    apply/trivIsetP => /= i j _ _ ij.
    have := tab_n i j Logic.I Logic.I ij.
    rewrite ifT; first by rewrite inE/=.
    rewrite ifT; first by rewrite inE/=.
    by [].
  - exact: mE.
  apply/ltW.
  under eq_bigr do rewrite lebesgue_measure_itv/= lte_fin ifT // ?(ablt n _ (ltn_ord _))// -EFinD.
  by rewrite sumEFin lte_fin; exact: d_prop.
(* lemma? *)
have image_E : forall i, (f @` (E_ i)) = \big[setU/set0]_(k < n_ i)f @` `](ab_ i k).1, (ab_ i k).2[%classic.
  move=> i.
  apply/seteqP; split => [y/= [x + <-{y}]|].
    rewrite /E_ => /mem_set/big_ord_setUP[j xj].
    apply:set_mem.
    apply/big_ord_setUP; exists j.
    rewrite inE/=.
    exists x => //.
    by rewrite inE in xj.
  move=> y/= /mem_set/big_ord_setUP[j].
  rewrite inE/= => -[x xj] <-{y}.
  exists x => //; rewrite /E_.
  apply:set_mem.
  by apply/big_ord_setUP; exists j; rewrite inE.
have imfitv n k : (k < n_ n)%N -> exists b0 b1,
  (f @` `](ab_ n k).1, (ab_ n k).2[ =
     [set` Interval (BSide b0 (f (ab_ n k).1)) (BSide b1 (f (ab_ n k).2))]).
  move=> knn.
  have := @continuous_nondecreasing_image_itvoo_itv _ (ab_ n k).1 (ab_ n k).2 f.
  by move/(_ (ablt n k knn) (Hc n k knn) (Hhomo n k knn)).
have mimf n k :(k < n_ n)%N -> R.-open.-measurable (f @` `](ab_ n k).1, (ab_ n k).2[%classic).
  move=> knn.
  by move: (imfitv n k knn) => [b0 [b1]] ->.
have mfE : forall i, R.-open.-measurable (f @` (E_ i)).
  move=> i.
  rewrite image_E.
  apply: bigsetU_measurable.
  move=> /= k _.
  exact: mimf.
have image_G : forall i, (f @` (G_ i)) = \bigcup_(k in [set j | (i <= j)%N]) (f @` (E_ k)).
  move=> i.
  apply/seteqP; split => [y/= [x + <-{y}]|].
      move=> [j /= ij Ejx].
      exists j => //=.
      by exists x.
    move=> _ [j /= ij [x Ejx <-]].
    exists x => //.
    by exists j.
have mA0 : mu A = 0.
  rewrite /A.
  have : (mu \o G_) x @[x --> \oo] --> 0%E.
    rewrite /=.
    have : \forall k \near \oo, (cst 0 k <= (mu \o G_) k <= (delta_0 k.-1)%:E)%E.
      near=> k => /=.
      rewrite measure_ge0 /=.
      apply: (@le_trans _ _ (\big[+%E/0%E]_(k <= j <oo) (mu (E_ j))%E)).
        rewrite (_: G_ k = \bigcup_n G_ (n + k)%N).
          apply/seteqP; split.
          + by exists 0%N.
          + apply: bigcup_sub => n _.
            apply: bigcup_sub => j /= nkj.
            apply: bigcup_sup => /=.
            by rewrite (leq_trans _ nkj)// leq_addl.
        rewrite -nneseries_addn; first by move=> i; by [].
        apply: measure_sigma_subadditive.
            by move=> n; exact: mE.
          by apply: bigcup_measurable => n _; exact: mG.
        move=> x.
        move=> [/= i _] [j /= ikj Ejx].
        exists (j - k)%N => //.
        by rewrite subnK// (leq_trans _ ikj)// leq_addl.
      rewrite [leRHS](_:_ = (\sum_(k <= j <oo) (delta_0 j)%:E)%E).
        apply: esym.
        apply: cvg_lim => //.
        rewrite d_geo0; first by near: k; exists 1%N.
        rewrite /geometric /=.
        rewrite -[X in _ --> (X * _)%:E]H1 mulrAC -exprS.
        rewrite -(cvg_shiftn k) /=.
        rewrite [X in X @ _ --> _](_:_= (fun n => (@series R (geometric (2^-1 ^+ k.+1) 2^-1) n)%:E)).
          apply/funext => n.
          rewrite /series /= sumEFin.
          rewrite -{1}(add0n k) big_addn addnK.
          congr (_%:E).
          apply: eq_bigr => i _.
          rewrite -exprD addSn addnC.
          by rewrite /delta_0 -exprVn.
        apply: cvg_EFin; first by apply: nearW.
        by apply: cvg_geometric_series.
      rewrite -nneseries_addn; first by [].
      rewrite -[leRHS]nneseries_addn.
        move=> i.
        rewrite lee_fin.
        rewrite /delta_0.
        apply/ltW.
        exact: delta_0_ge0.
      apply: lee_lim.
      - apply: ereal_nondecreasing_is_cvgn.
        exact: ereal_nondecreasing_series.
      - apply: ereal_nondecreasing_is_cvgn.
        apply: ereal_nondecreasing_series => i _ _.
        rewrite lee_fin.
        rewrite /delta_0.
        apply/ltW.
        exact: delta_0_ge0.
      apply: nearW => /= n.
      exact: lee_sum.
    move/squeeze_cvge.
    apply => //.
    apply: cvg_trans.
      apply: near_eq_cvg; near=> k.
      rewrite d_geo0; first by near: k; exists 1%N.
      reflexivity.
    apply: cvg_EFin; first by near=> k.
    exact: cvg_geometric.
  suff: (mu \o G_) x @[x --> \oo] --> mu (\bigcap_n G_ n).
    by move=> /cvg_unique /[apply]; exact.
  apply: nonincreasing_cvg_measure => //=.
  - rewrite (@le_lt_trans _ _ (\sum_(0 <= i <oo) mu (E_ i))%E)//.
      apply: measure_sigma_subadditive => //.
      rewrite /G_.
      by apply: bigcup_sub => i _; exact: bigcup_sup.
    apply: (@le_lt_trans _ _ 1%E); last exact: ltry.
    rewrite (_ : 1%E = (\big[+%R/0%R]_(0 <= i <oo) (delta_0 i)%:E)); last first.
      exact: lee_nneseries.
    apply/esym.
    rewrite -H1.
    apply/cvg_lim => //.
    apply: cvg_EFin.
      by apply: nearW => n; rewrite sumEFin.
    under eq_cvg => n.
      rewrite /= sumEFin.
      under eq_bigr do rewrite d_geo.
      over.
    exact: cvg_geometric_series.
  - by apply: bigcapT_measurable => ?; exact: mG.
  - move=> s k sk.
    rewrite /G_.
    rewrite subsetEset.
    apply: bigcup_sub => n /= kn.
    apply: bigcup_sup => /=.
    exact: (@le_trans _ _ k).
have mfA0 : mu (f @` A) = 0.
  apply: lf.
  - move=> r Ar.
    rewrite /A /bigcap /= /G_ /= in Ar.
    have [i _] := Ar O I.
    rewrite /E_.
    rewrite -bigcup_seq/= => -[j /= Hj].
    exact: (H3 _ _ _).2.
  - exact: bigcapT_measurable.
  - exact: mA0.
(* where we used to use get_nice_image_itv *)
have H n : (e0%:num%:E <= mu (f @` G_ n))%E.
  apply: (@le_trans _ _ (mu (f @` E_ n))); last first.
    rewrite le_measure ?inE//=.
    - rewrite image_E.
      apply: bigsetU_measurable => //= i _.
      exact: mimf.
    - rewrite image_G.
      apply: bigcup_measurable => //= i _.
      rewrite image_E.
      apply: bigsetU_measurable => //= j _.
      exact: mimf.
    - apply: image_subset => //.
      rewrite /G_.
      by apply: bigcup_sup => /=.
  have : mu (f @` E_ n) = (\sum_(k < n_ n) `|f (ab_ n k).2 - f (ab_ n k).1|)%:E.
    have ab_1 (j : 'I_(n_ n)) : (ab_ n j).1 \in `[a, b].
      apply: (subset_neitv_oocc (ablt _ _ (ltn_ord j)) (absub _ _ _)) => //=.
      by rewrite in_itv/= lexx/= (ltW (ablt _ _ (ltn_ord j))).
    have ab_2 (j : 'I_(n_ n)) : (ab_ n j).2 \in `[a, b].
      apply: (subset_neitv_oocc (ablt _ _ (ltn_ord j)) (absub _ _ _)) => //=.
      by rewrite in_itv/= lexx/= (ltW (ablt _ _ (ltn_ord j))).
    (* not in paper <- TODO: explain? *)
    transitivity (\sum_(k < n_ n) mu (f @` `](ab_ n k).1, (ab_ n k).2[%classic)).
    (* /not in paper *)
      rewrite [X in mu [set f x | x in X]] (_ : _ =
          \bigcup_(k < n_ n) `](ab_ n k).1, (ab_ n k).2[%classic).
        by rewrite bigcup_mkord.
      rewrite image_bigcup [X in mu X](_ : _ =
        \big[setU/set0]_(i < n_ n) [set f x | x in `](ab_ n i).1, (ab_ n i).2[]).
        by rewrite bigcup_mkord.
      have : forall i : 'I_(n_ n), exists b01,
        f @` `](ab_ n i).1, (ab_ n i).2[ = set01 b01.1 (f (ab_ n i).1) `|`
                                           `]f (ab_ n i).1, f (ab_ n i).2[ `|`
                                           set01 b01.2 (f (ab_ n i).2).
        move=> i.
        have K1 : {within `[(ab_ n i).1, (ab_ n i).2], continuous f}.
          apply: continuous_subspaceW cf => //.
          apply: subset_neitv_oocc.
            exact: (H3 _ _ _).1.
          exact: (H3 _ _ _).2.
        have K2 : {in `](ab_ n i).1, (ab_ n i).2[ &, {homo f : x y / (x <= y)%O}}.
          exact: (Hhomo _ _ _).
        have [b0 [b1 K3]] := continuous_nondecreasing_image_itvoo_itv (H3 _ _ (ltn_ord i)).1 K1 K2.
        have : f (ab_ n i).1 <= f (ab_ n i).2.
          by rewrite nndf//; exact/ltW/(H3 _ _ _).1.
        rewrite le_eqVlt => /predU1P[K|K].
        - move: b0 b1 K3 => [|] [|] /= ->.
          + exists (false, false) => //=.
            by rewrite setU0 set0U K set_itv_ge ?bnd_simp// set_itv_ge ?bnd_simp.
          + exists (true, false) => //=.
            rewrite setU0 K [in RHS]set_itv_ge ?bnd_simp//= setU0.
            by rewrite set_itv1.
          + exists (false, false) => //=.
            by rewrite setU0 set0U K set_itv_ge ?bnd_simp// set_itv_ge ?bnd_simp.
          + exists (false, false) => //=.
            by rewrite setU0 set0U K set_itv_ge ?bnd_simp// set_itv_ge ?bnd_simp.
       -  move: b0 b1 K3 => [|] [|] /= ->.
          + exists (true, false) => /=.
            by rewrite setU0 setU1itv//= bnd_simp.
          + exists (true, true) => /=.
            rewrite setU1itv ?bnd_simp//=.
            rewrite setUitv1 ?bnd_simp//=.
            exact/ltW.
          + exists (false, false) => /=.
            by rewrite set0U setU0.
          + exists (false, true) => /=.
            by rewrite set0U setUitv1 ?bnd_simp.
      move=> /choice[endpoints Hendpoints].
      under eq_bigr do rewrite Hendpoints//.
      transitivity (mu (\big[setU/set0]_(i < n_ n) `](f (ab_ n i).1), (f (ab_ n i).2)[%classic)).
        rewrite [X in mu X](_ : _ =
          ((\big[setU/set0]_i set01 (endpoints i).1 (f (ab_ n i).1))
            `|`
           (\big[setU/set0]_i set01 (endpoints i).2 (f (ab_ n i).2))
             `|`
           (\big[setU/set0]_(i < n_ n) `](f (ab_ n i).1), (f (ab_ n i).2)[%classic))).
          rewrite !big_split/=.
          by rewrite setUAC.
        rewrite measureU//=.
        + apply: measurableU.
          * apply: bigsetU_measurable => i _.
            by rewrite /set01; case: ifPn.
          * apply: bigsetU_measurable => i _.
            by rewrite /set01; case: ifPn.
        + exact: bigsetU_measurable.
        + rewrite -subset0 => x [[]].
          * move=> /mem_set /big_ord_setUP[i].
            rewrite inE /set01; case: ifPn => //= i1 ->{x}.
            move=> /mem_set /big_ord_setUP[j].
            rewrite inE/= in_itv/=.
            have [ij|ij|ij] := ltgtP i j.
            - have H : f (ab_ n i).1 <= f (ab_ n j).1.
                rewrite nndf// (le_trans _ (ordered _ i j _))//.
                exact/ltW/ablt.
              by rewrite ltNge H.
            - have H : f (ab_ n j).2 <= f (ab_ n i).1.
                by rewrite nndf// (le_trans _ (ordered _ j i _)).
              move=> /andP[_].
              by rewrite ltNge H.
            by rewrite ij ltxx.
          * move=> /mem_set /big_ord_setUP[i].
            rewrite inE /set01; case: ifPn => //= i1 ->{x}.
            move=> /mem_set /big_ord_setUP[j].
            rewrite inE/= in_itv/=.
            have [ij|ij|ij] := ltgtP i j.
            - have H : f (ab_ n i).2 <= f (ab_ n j).1.
                by rewrite nndf// (le_trans _ (ordered _ i j _)).
              by rewrite ltNge H.
            - rewrite !ltNge.
              have -> : f (ab_ n j).2 <= f (ab_ n i).2.
                rewrite nndf// (le_trans (ordered _ j i ij))//.
                exact/ltW/ablt.
              by rewrite andbF.
            - by rewrite ij ltxx andbF.
        + rewrite measureU0//=.
          * apply: bigsetU_measurable => i _.
            by rewrite /set01; case: ifPn.
          * apply: bigsetU_measurable => i _.
            by rewrite /set01; case: ifPn.
          * by apply: measure_bigsetU_set01.
          * rewrite [X in (X + _)%E](_ : _ = 0).
              exact: measure_bigsetU_set01.
            by rewrite add0e.
      rewrite measure_semi_additive_ord//=.
      - apply/trivIsetP => /= i j _ _.
        rewrite neq_lt => /orP[ij|ij].
        + rewrite -subset0 => x []/=.
          rewrite !in_itv/= => /andP[K1 K2] /andP[K3 K4].
          have := lt_trans K3 K2.
          apply/negP.
          by rewrite -leNgt nndf// (le_trans (ordered _ i j ij)).
        + rewrite -subset0 => x []/=.
          rewrite !in_itv/= => /andP[K1 K2] /andP[K3 K4].
          have := lt_trans K1 K4.
          apply/negP.
          by rewrite -leNgt nndf// (le_trans (ordered _ _ _ ij)).
      - exact: bigsetU_measurable.
      - apply: eq_bigr => i _.
        have /(_ _ _)[| | |] := @continuous_nondecreasing_image_itvoo_itv _ (ab_ n i).1 (ab_ n i).2 f.
        + exact: (ablt _ _ (ltn_ord i)).
        + apply: continuous_subspaceW cf => //.
        + apply: subset_neitv_oocc.
          * exact: (ablt _ _ (ltn_ord i)).
          * exact: (H3 _ _ _).2.
        + exact: (Hhomo _ _ _).
      move=> b0 [b2 H].
      rewrite H/=.
      rewrite [RHS]lebesgue_measure_itv//=.
      rewrite lte_fin.
      by rewrite [LHS]lebesgue_measure_itv//=.
    (* end of looooong transitivity step *)
    rewrite -sumEFin.
    apply/eq_bigr => i _.
    have /(_ _ _)[| | |] := @continuous_nondecreasing_image_itvoo_itv _ (ab_ n i).1 (ab_ n i).2 f.
    + exact: (ablt _ _ (ltn_ord i)).
    + apply: continuous_subspaceW cf => //.
      apply: subset_neitv_oocc.
      * exact: (ablt _ _ (ltn_ord i)).
      * exact: (H3 _ _ _).2.
      * exact: (Hhomo _ _ _).
    move=> b0 [b1 H].
    rewrite H/=.
    rewrite [LHS]lebesgue_measure_itv// lte_fin /=.
    rewrite lt_neqAle.
    have [K1|K1] := eqVneq (f (ab_ n i).1) (f (ab_ n i).2).
      by rewrite /= K1 subrr normr0.
    rewrite /= nndf//.
    exact/ltW/ablt.
  - rewrite ger0_norm.
      rewrite subr_ge0 nndf//.
      exact/ltW/ablt.
    by rewrite EFinB.
  move=> ->.
  by rewrite lee_fin e0_prop.
have muFG0 : mu (\bigcap_k [set f x | x in G_ k]) = 0.
  have ndF : {in `[a, b]%classic &, {homo F : n m / n <= m}}.
    by move=> x y /[!inE] xab yab xy; exact: nndf.
  have Gopen k : open (G_ k).
    apply: bigcup_open => i _.
    rewrite /E_ -(bigcup_mkord (n_ i) (fun k => `](ab_ i k).1, (ab_ i k).2[%classic)).
    by apply: bigcup_open => j _; exact: interval_open.
  have Gab k : G_ k `<=` `]a, b[.
    apply: bigcup_sub => i /= ki.
    rewrite /E_.
    rewrite -(bigcup_mkord (n_ i) (fun k => `](ab_ i k).1, (ab_ i k).2[%classic)).
    apply: bigcup_sub => j /= jni.
    move : (absub i j jni).
    rewrite open_subsetE.
      exact: interval_open.
    by rewrite interior_itv.
  have := @measure_image_nondecreasing_fun R a b F ab nndf G_ cf Gab Gopen.
  by rewrite /= -/A mfA0.
have mfG_ n : lebesgue_display.-measurable (f @` G_ n).
  rewrite image_G; apply: bigcup_measurable => k /= nk.
  by rewrite image_E; apply: bigsetU_measurable => //= i _; exact: mimf.
have : (e0%:num%:E <= limn (fun n => mu (F @` G_ n)))%E.
  apply: lime_ge; last exact: nearW.
  apply: ereal_nonincreasing_is_cvgn; apply/nonincreasing_seqP => n.
  rewrite le_measure ?inE //=.
  apply: image_subset; apply: bigcup_sub => j /= mj x Ejx.
  by exists j => //=; exact: leq_trans mj.
suff: mu (\bigcap_k (f @` G_ k)) = lim (mu (F @` G_ n) @[n --> \oo]).
  by move=> <-; apply/negP; rewrite -ltNge muFG0.
apply/esym/cvg_lim => //=; apply: nonincreasing_cvg_measure => //=.
- apply: (@le_lt_trans _ _ (mu `[F a, F b])); last first.
    rewrite lebesgue_measure_itv//= lte_fin.
    rewrite (lt_neqAle (f a)) nndf ?andbT.
    + by rewrite bound_itvE ltW.
    + by rewrite bound_itvE ltW.
    + exact: ltW.
    + by case: ifPn => //; rewrite -EFinB ltry.
  rewrite le_measure//= ?inE// => x/= [r [i _]].
  rewrite /E_ -(bigcup_mkord (n_ i) (fun k => `](ab_ i k).1, (ab_ i k).2[%classic)).
  move=> -[j jni]/= ijr <-{x}.
  apply: (continuous_nondecreasing_image_itvcc (ltW ab)) => //.
  by exists r => //=; exact: (absub _ _ _ _ ijr).
- exact: bigcapT_measurable.
- move=> x y xy; apply/subsetPset; apply: image_subset; rewrite /G_.
  apply: bigcup_sub => i/= yi.
  by apply: bigcup_sup => //=; rewrite (leq_trans xy).
Unshelve. all: end_near. Qed.

End Banach_Zarecki_lemma7.
