From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_boot all_order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import mathcomp_extra boolp contra classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure numfun realfun.
From mathcomp Require Import absolute_continuity.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 4)                                         *)
(*                                                                            *)
(*   cplt_hull P            == A relative complement of P in convex hull of P.*)
(*   contiguous_intervals P == A countable family of component intervals of   *)
(*                             cplt_hull P, called as "intervals contiguous   *)
(*                             to P" in Ene's Proof.                          *)
(* ref: https://projecteuclid1.org/journals/real-analysis-exchange/volume-23/ *)
(*issue-1/An-Elementary-Proof-of-the-Banach-Zarecki-Theorem/rae/              *)
(*1337086099.full*)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma image_bigcup_disjoint T U (f : T -> U) I (D : set I)
   (F : I -> set T) :
  trivIset D F -> f @` (\bigcup_(i in D) F i) = \bigcup_(i in D) f @` F i.
Proof.
move=> DS.
apply/seteqP; split => [_ [x [i Di Six <-]]|_ [i Di [x Six <-]]].
  by exists i.
by exists x => //; exists i.
Qed.

Section lemma4_preliminaries.
Context {R : realType}.

Lemma eq_Rhull_itvccP A (a b : R) :
  Rhull A = `[a, b] <->
  [/\ has_lbound A, A (inf A) & inf A = a] /\
  [/\ has_ubound A, A (sup A) & sup A = b].
Proof.
split.
- rewrite /Rhull.
  case: ifP => // /asboolP haslbA.
  case: ifP => // /asboolP hasubA.
  have [/[dup]infP /asboolP -> /= |/asboolF -> //] := pselect (A (inf A)).
  have [/[dup]supP /asboolP -> /= |/asboolF -> //] := pselect (A (sup A)).
  case => infPa supPb.
  by split; split.
- move=> [[haslbA Ainf infa] [hasubA Asup supa]].
  rewrite /Rhull.
  move/asboolP: haslbA ->; move/asboolP: hasubA ->.
  move/asboolP: Ainf ->; move/asboolP: Asup ->.
  by rewrite infa supa.
Qed.

Lemma interval_ooS (A : set R) : inf A <= sup A -> `](inf A), (sup A)[ `<=` [set` Rhull A].
Proof.
move=> infsup r/= rA.
rewrite /Rhull.
case: ifPn => // lA.
  case: ifPn => // uA.
    rewrite !in_itv/= negbK.
    have [Ainf|Ainf]/= := boolP (`[< A (inf A) >]);
      have [Asup|Asup]/= := boolP (`[< A (sup A) >]); by rewrite !(itvP rA).
  rewrite !in_itv/= andbT.
  have [Asup|Asup]/= := boolP (`[< A (inf A) >]); by rewrite !(itvP rA).
case: ifPn => // uA.
rewrite in_itv/= negbK.
have [Asup|Asup]/= := boolP (`[< A (sup A) >]); by rewrite !(itvP rA).
Qed.

Local Open Scope ereal_scope.

Lemma interval_ooS_old (A : interval R) : A.1 <= A.2 -> `](fine A.1), (fine A.2)[ `<=` [set` A].
Proof.
move: A => [r s].
move: r => [[|]r|[|]]; move: s => [[|]s|[|]]//= rs x/=; rewrite ?in_itv//=.
- by move=> /andP[/ltW -> ->].
- by move=> /andP[/ltW -> /ltW ->].
- by move=> /andP[/ltW ->].
- by move=> /andP[-> /ltW ->].
- by move=> /andP[->].
- by move=> /andP[_ ->].
- by move=> /andP[_ /ltW ->].
- by move=> /andP[] /lt_trans /[apply]; rewrite ltxx.
- by move=> /andP[] /lt_trans /[apply]; rewrite ltxx.
Qed.

Lemma Rull_fst_snd (A : set R) : (Rhull A).1 <= (Rhull A).2.
Proof.
rewrite /Rhull; case: ifPn => /asboolP lA; case: ifPn => // /asboolP uA /=.
- by rewrite lee_fin has_bound_inf_sup//; exact/set0P.
- by rewrite leey.
- by rewrite leNye.
Qed.

(* TODO: PR *)
Lemma hasNlb_ereal_inf (A : set R) :
  ~ has_lbound A -> A !=set0 -> ereal_inf (EFin @` A) = -oo.
Proof.
move=> hasNlbA A0.
rewrite ereal_infEN.
rewrite [X in - ereal_sup X = _](_ : _ =
  (EFin @` (-%R @` A))); last first.
  rewrite eqEsubset; split.
  - move=> _ [_ [r Ar <-] <-].
    by exists (- r)%R.
  - move=> _ [_ [r Ar <-] <-].
    by exists r%:E.
rewrite hasNub_ereal_sup//.
- by rewrite -has_lb_ubN.
- exact: image_nonempty.
Qed.

Lemma trivIset_contiguous_intervals (P : set R) :
  has_lbound P -> has_ubound P ->
  let a_ := contiguous_intervals1 P : (R) ^nat in
  let b_ := contiguous_intervals2 P : (R) ^nat in
  trivIset [set: nat] (fun i : nat => `]((a_ i)), ((b_ i))[%classic).
Proof.
move=> lP uP.
rewrite /= /contiguous_intervals1 /contiguous_intervals2.
apply/trivIsetP => i j _ _ ij.
have /trivIsetP/(_ i j Logic.I Logic.I ij) := @disjoint_contiguous_intervals _ P.
apply: subsetI_eq0. (* TODO: generalize this lemma to trivIset *)
- have /is_intervalP H := @is_interval_contiguous_intervals _ P i.
  rewrite [X in _ `<=` X]H.
   apply: interval_ooS.
   rewrite has_bound_inf_sup//.
   by apply: has_lbound_contiguous_intervals.
   by apply: has_ubound_contiguous_intervals.
- have /is_intervalP H := @is_interval_contiguous_intervals _ P j.
  rewrite [X in _ `<=` X]H.
  apply: interval_ooS.
  rewrite has_bound_inf_sup//.
  by apply: has_lbound_contiguous_intervals.
  by apply: has_ubound_contiguous_intervals.
Qed.

End lemma4_preliminaries.

Section lemma4.
Context {R: realType}.
Variables a b : R.
Hypothesis ab : a <= b.
Local Notation mu := (@completed_lebesgue_measure R).
Local Open Scope ereal_scope.

Lemma lemma4 (f : R -> R) (P : set R) :
  is_interval (f @` `[a, b]) ->
  (* perfect_set P *) closed P ->
 (*  a = inf P -> b = sup P -> *)
  Rhull P = `[a, b] ->
  let a_ := contiguous_intervals1 P in
  let b_ := contiguous_intervals2 P in
  `|f b - f a|%:E <= mu (f @` `[a, b])
     <= (mu^*)%mu (f @` P) +
        \sum_(0 <= i <oo) oscillation f `[(a_ i), (b_ i)]%classic.
Proof.
move=> fab closedP.
move/[dup]/eq_Rhull_itvccP => [[haslbP Pinf infa] [hasubP Psup supa]] Pab.
have compactP : compact P.
  apply: Rbounded_closed_compact => //.
  by rewrite Rbounded_setE.
set a_ := contiguous_intervals1 P.
set b_ := contiguous_intervals2 P.
have H1 : f @` `[a, b] = (f @` P) `|` \bigcup_i f @` `](a_ i), (b_ i)[.
  rewrite -image_bigcup_disjoint; last first.
    exact: trivIset_contiguous_intervals.
  rewrite -image_setU.
  congr (f @` _).
  apply/seteqP; split; last first.
    rewrite -Pab.
    rewrite subUset; split; first exact: sub_Rhull.
    apply: bigcup_sub => i _.
    have -> : `]((a_ i)), ((b_ i))[%classic =
                   [set` Rhull (contiguous_intervals P i)].
      rewrite /Rhull.
      rewrite ifT; last exact/asboolP/has_lbound_contiguous_intervals.
      rewrite ifT; last exact/asboolP/has_ubound_contiguous_intervals.
      congr ([set` Interval (BSide _ _) (BSide _ _)]); apply: eq_fun => _.
      - apply/esym/asboolF.
        apply: open_haslb_memNinf.
        + exact: has_lbound_contiguous_intervals.
        + exact: open_contiguous_intervals.
      - apply/esym/asboolP.
        apply: open_hasub_memNsup.
        + exact: has_ubound_contiguous_intervals.
        + exact: open_contiguous_intervals.
    rewrite RhullK; last first.
      rewrite inE.
      exact: is_interval_contiguous_intervals.
    apply: (subset_trans (@contiguous_intervalsS _ P i)).
    exact: cplt_hull_subset_Rhull.
  rewrite /a_.
  rewrite -bigcup_contiguous_intervals_fine//.
  rewrite setDUK; last exact: sub_Rhull.
  by rewrite Pab.
apply/andP; split.
  (* wlog? *)
  have [fafb|] := pselect (f a < f b)%R.
    have -> : `|f b - f a|%:E = mu `[f a, f b].
      rewrite completed_lebesgue_measure_itv/= lte_fin fafb -EFinD.
      move: fafb.
      rewrite -subr_gt0.
      by move/ltW/normr_idP ->.
    apply: le_outer_measure => /= x/= xfab.
    apply: (fab (f a) (f b)).
    - by exists a => //=; rewrite bound_itvE.
    - by exists b => //=; rewrite bound_itvE.
    - by rewrite in_itv/= in xfab.
    move/negP; rewrite -leNgt.
    rewrite le_eqVlt => /predU1P[-> |].
      by rewrite subrr normr0 measure_ge0.
  rewrite -normrN opprB => fbfa.
  have -> : `|f a - f b|%:E = mu `[f b, f a].
    rewrite completed_lebesgue_measure_itv/= lte_fin fbfa -EFinD.
    move: fbfa.
    rewrite -subr_gt0.
    by move/ltW/normr_idP ->.
  apply: le_outer_measure => /= x/= xfba.
  apply: (fab (f b) (f a)).
  - by exists b => //=; rewrite bound_itvE.
  - by exists a => //=; rewrite bound_itvE.
  - by rewrite in_itv/= in xfba.
rewrite -measurable_mu_extE; last first.
  apply: sub_caratheodory.
  rewrite -(@RhullK _ (f @` `[a, b]))//.
  by rewrite inE.
rewrite H1.
apply: (@le_trans _ _ (mu^*%mu [set f x | x in P] +
         mu^*%mu (\bigcup_i [set f x | x in `](a_ i), (b_ i)[]))).
  exact: outer_measureU2.
apply: leeD2l.
apply: le_trans.
  exact: outer_measure_sigma_subadditive.
rewrite /=.
apply: lee_nneseries; first by move=> i _ _; exact: outer_measure_ge0.
move=> n _.
rewrite /oscillation.
case: ifPn => [/eqP ab0|ab0].
  have anbn : ((a_ n) > (b_ n))%R.
    rewrite ltNge; contra: ab0 => anbn.
    apply/set0P; exists ((a_ n)).
    by rewrite /= in_itv/= lexx anbn.
  rewrite set_itv_ge ?bnd_simp -?leNgt//; last exact/ltW.
  by rewrite image_set0 mu_ext0.
rewrite [leRHS](_ : _ =
       mu^*%mu [set` Rhull (f @` `[((a_ n)), ((b_ n))] )]).
  apply: le_outer_measure.
  apply: subset_trans (@sub_Rhull _ _).
  apply: image_subset.
  exact: subset_itv_oo_cc.
rewrite measurable_mu_extE/=; last first.
  apply: sub_caratheodory.
  exact: measurable_itv.
rewrite completed_lebesgue_measure_itv.
have fab0 : [set f x | x in `[(a_ n), (b_ n)]] !=set0.
  exists (f ((a_ n))) => //.
  exists ((a_ n)) => //=.
  rewrite boundl_in_itv//= bnd_simp.
  exact: contiguous_intervals1_le_contiguous_intervals2.
have [hasubf|hasNubf] :=
  pselect (has_ubound (f @` `[((a_ n)), ((b_ n))])); last first.
  rewrite -image_comp hasNub_ereal_sup//.
  rewrite addye; last first.
    apply/eqP.
    move/eqe_oppLRP => /=.
    move/ereal_inf_pinfty.
    apply/not_forallP; rewrite not_notE.
    have [y [x/= xab fax]] := fab0.
    by exists y%:E; rewrite ?not_implyP; split => //; exists y => //; exists x.
  rewrite ifT; last first.
    rewrite /=; move/asboolF : (hasNubf) => ->.
    by case: ifP => // _; exact: ltry.
  rewrite /=; move/asboolF : (hasNubf) => ->.
  by case: ifP.
have [haslbf|hasNlbf] :=
   pselect (has_lbound (f @` `[(a_ n), (b_ n)])); last first.
  rewrite -[X in _ - ereal_inf X = _]image_comp hasNlb_ereal_inf//; last first.
  rewrite ifT; last first.
    rewrite /=; move/asboolF: (hasNlbf) => ->.
    move/asboolP: (hasubf) => ->; exact: ltNyr.
  rewrite /=; move/asboolF: (hasNlbf) => -> /=.
  have supNy: ereal_sup ((EFin \o f) @` `[((a_ n)), ((b_ n))]) != -oo.
    apply/eqP; move/ereal_sup_ninfty; apply/not_forallP; rewrite not_notE.
    have [y [x/= xab fax]] := fab0.
    by exists y%:E; rewrite ?not_implyP; split => //; exists x=> //; congr EFin.
  by case: ifP; rewrite addey.
rewrite /Rhull; move/asboolP: (hasubf) ->; move/asboolP: (haslbf) -> => //.
case: ifP => /=; last first.
- move/negP/negP; rewrite -leNgt.
  rewrite le_eqVlt => /predU1P[|]; last first.
  + rewrite lte_fin ltNge => /negP Ninfsup.
    by have := has_bound_inf_sup haslbf hasubf.
  + rewrite -ereal_sup_EFin -?ereal_inf_EFin// image_comp => ->;
    rewrite subee//.
    by rewrite -image_comp ereal_inf_EFin.
- move=> _; rewrite EFinN -ereal_sup_EFin -?ereal_inf_EFin// 2?image_comp//.
Qed.

Local Close Scope ereal_scope.

Let ex_perfect_set (cmf : cumulative R R) (cZ : set R) :
  let f := cmf in
  cZ `<=` `[a, b] ->
  {within `[a, b], continuous f} ->
  {in `[a, b], {homo f : x y / (x <= y)}} ->
  bounded_variation a b f ->
  exists n, exists I : nat -> R * R,
  (forall i, trivIset setT (fun i => `[(I i).1, (I i).2]%classic) /\
    `](I i).1, (I i).2[ `<=` cZ) /\
     (\sum_(0 <= i < n) `|f (I i).2 - f (I i).1|)%:E
     = completed_lebesgue_stieltjes_measure f cZ.
Proof.
Abort.

End lemma4.

Section lemma4_cover.
Context {R: realType}.
Variables a b : R.
Hypothesis ab : a <= b.
Local Notation mu := (@completed_lebesgue_measure R).

Local Open Scope ereal_scope.

Lemma lemma4_cover (f : R -> R) (P : set R) (xy : nat -> R * R) :
  is_interval (f @` `[a, b]) ->
  (* perfect_set P *) closed P ->
 (*  a = inf P -> b = sup P -> *)
  Rhull P = `[a, b] ->
  (forall n, (xy n).1 <= (xy n).2)%R ->
 `[a, b]%classic `<=` P `|`
   (\bigcup_i `](xy i).1, (xy i).2[%classic) ->
  `|f b - f a|%:E <= mu (f @` `[a, b])
     <= (mu^*)%mu (f @` P) +
        \sum_(0 <= i <oo) oscillation f `[(xy i).1, (xy i).2]%classic.
Proof.
move=> fab closedP + xy12 abSubPxy.
move/[dup]/eq_Rhull_itvccP => [[haslbP Pinf infa] [hasubP Psup supa]] Pab.
have compactP : compact P.
  apply: Rbounded_closed_compact => //.
  by rewrite Rbounded_setE.
have H1 : f @` `[a, b] `<=` (f @` P) `|` \bigcup_i f @` `](xy i).1, (xy i).2[.
  rewrite -image_bigcup -image_setU.
  exact: image_subset.
apply/andP; split.
  (* wlog? *)
  have [fafb|] := pselect (f a < f b)%R.
    have -> : `|f b - f a|%:E = mu `[f a, f b].
      rewrite completed_lebesgue_measure_itv/= lte_fin fafb -EFinD.
      move: fafb.
      rewrite -subr_gt0.
      by move/ltW/normr_idP ->.
    apply: le_outer_measure => /= x/= xfab.
    apply: (fab (f a) (f b)).
    - by exists a => //=; rewrite bound_itvE.
    - by exists b => //=; rewrite bound_itvE.
    - by rewrite in_itv/= in xfab.
    move/negP; rewrite -leNgt.
    rewrite le_eqVlt => /predU1P[-> |].
      by rewrite subrr normr0 measure_ge0.
  rewrite -normrN opprB => fbfa.
  have -> : `|f a - f b|%:E = mu `[f b, f a].
    rewrite completed_lebesgue_measure_itv/= lte_fin fbfa -EFinD.
    move: fbfa.
    rewrite -subr_gt0.
    by move/ltW/normr_idP ->.
  apply: le_outer_measure => /= x/= xfba.
  apply: (fab (f b) (f a)).
  - by exists b => //=; rewrite bound_itvE.
  - by exists a => //=; rewrite bound_itvE.
  - by rewrite in_itv/= in xfba.
rewrite -measurable_mu_extE; last first.
  apply: sub_caratheodory.
  rewrite -(@RhullK _ (f @` `[a, b]))//.
  by rewrite inE.
apply: (le_trans (le_outer_measure mu^*%mu _ _ H1)).
apply: (le_trans (outer_measureU2 _ _ _)).
rewrite leeD2l//.
apply: (le_trans (outer_measure_sigma_subadditive _ _)).
apply: lee_nneseries => // n _.
rewrite [leLHS](_ : mu^*%mu (f @` `](xy n).1, (xy n).2[) =
                    mu (f @` `[(xy n).1, (xy n).2]))%E; last first.
  admit.
have isitv_xy : is_interval (f @` `[(xy n).1, (xy n).2]).
  admit.
set P' := [set (xy n).1; (xy n).2].
have cP' : closed P'.
  admit.
have RhullP' : Rhull P' = `[(xy n).1, (xy n).2].
  admit.

have := lemma4 (xy12 n) isitv_xy cP' RhullP'.
move/andP => [_].
have -> : mu^*%mu [set f x | x in P'] = 0.
  admit.
rewrite add0e.
move/le_trans; apply.
admit.
(*
rewrite le_outer_measure.
rewrite H1.
apply: (@le_trans _ _ (mu^*%mu [set f x | x in P] +
         mu^*%mu (\bigcup_i [set f x | x in `](a_ i), (b_ i)[]))).
  exact: outer_measureU2.
apply: leeD2l.
apply: le_trans.
  exact: outer_measure_sigma_subadditive.
rewrite /=.
apply: lee_nneseries; first by move=> i _ _; exact: outer_measure_ge0.
move=> n _.
rewrite /oscillation.
case: ifPn => [/eqP ab0|ab0].
  have anbn : ((a_ n) > (b_ n))%R.
    rewrite ltNge; contra: ab0 => anbn.
    apply/set0P; exists ((a_ n)).
    by rewrite /= in_itv/= lexx anbn.
  rewrite set_itv_ge ?bnd_simp -?leNgt//; last exact/ltW.
  by rewrite image_set0 mu_ext0.
rewrite [leRHS](_ : _ =
       mu^*%mu [set` Rhull (f @` `[((a_ n)), ((b_ n))] )]).
  apply: le_outer_measure.
  apply: subset_trans (@sub_Rhull _ _).
  apply: image_subset.
  exact: subset_itv_oo_cc.
rewrite measurable_mu_extE/=; last first.
  apply: sub_caratheodory.
  exact: measurable_itv.
rewrite completed_lebesgue_measure_itv.
have fab0 : [set f x | x in `[(a_ n), (b_ n)]] !=set0.
  exists (f ((a_ n))) => //.
  exists ((a_ n)) => //=.
  rewrite boundl_in_itv//= bnd_simp.
  exact: intervals1_le_contiguous_intervals2.
have [hasubf|hasNubf] :=
  pselect (has_ubound (f @` `[((a_ n)), ((b_ n))])); last first.
  rewrite -image_comp hasNub_ereal_sup//.
  rewrite addye; last first.
    apply/eqP.
    move/eqe_oppLRP => /=.
    move/ereal_inf_pinfty.
    apply/not_forallP; rewrite not_notE.
    have [y [x/= xab fax]] := fab0.
    by exists y%:E; rewrite ?not_implyP; split => //; exists y => //; exists x.
  rewrite ifT; last first.
    rewrite /=; move/asboolF : (hasNubf) => ->.
    by case: ifP => // _; exact: ltry.
  rewrite /=; move/asboolF : (hasNubf) => ->.
  by case: ifP.
have [haslbf|hasNlbf] :=
   pselect (has_lbound (f @` `[(a_ n), (b_ n)])); last first.
  rewrite -[X in _ - ereal_inf X = _]image_comp hasNlb_ereal_inf//; last first.
  rewrite ifT; last first.
    rewrite /=; move/asboolF: (hasNlbf) => ->.
    move/asboolP: (hasubf) => ->; exact: ltNyr.
  rewrite /=; move/asboolF: (hasNlbf) => -> /=.
  have supNy: ereal_sup ((EFin \o f) @` `[((a_ n)), ((b_ n))]) != -oo.
    apply/eqP; move/ereal_sup_ninfty; apply/not_forallP; rewrite not_notE.
    have [y [x/= xab fax]] := fab0.
    by exists y%:E; rewrite ?not_implyP; split => //; exists x=> //; congr EFin.
  by case: ifP; rewrite addey.
rewrite /Rhull; move/asboolP: (hasubf) ->; move/asboolP: (haslbf) -> => //.
case: ifP => /=; last first.
- move/negP/negP; rewrite -leNgt.
  rewrite le_eqVlt => /predU1P[|]; last first.
  + rewrite lte_fin ltNge => /negP Ninfsup.
    by have := has_bound_inf_sup haslbf hasubf.
  + rewrite -ereal_sup_EFin -?ereal_inf_EFin// image_comp => ->;
    rewrite subee//.
    by rewrite -image_comp ereal_inf_EFin.
- move=> _; rewrite EFinN -ereal_sup_EFin -?ereal_inf_EFin// 2?image_comp//.
*)
Admitted.

End lemma4_cover.
