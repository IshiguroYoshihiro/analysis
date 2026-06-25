From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_boot all_order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean perm finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality.
From mathcomp Require Import reals constructive_ereal topology normedtype.
From mathcomp Require Import ereal sequences.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import absolute_continuity banach_zarecki_lemma2.
From mathcomp Require Import banach_zarecki_lemma3 banach_zarecki_lemma5.
From mathcomp Require Import banach_zarecki_lemma4 (* for contiguous intervals *).

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 6)                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma finite_seqP_new {T : eqType} A :
   finite_set A <-> exists2 s : seq T, uniq s & A = [set` s].
Proof.
elim/eqPchoice: T => T in A *; rewrite finite_fsetP.
split=> [[X ->]|[s us ->]]; first by exists X.
by exists [fset x | x in s]%fset; apply/seteqP; split=> x /=; rewrite inE.
Qed.

Section lemmas.
Context {R : realType}.
Local Notation mu := (@completed_lebesgue_measure R).

Lemma is_subset1_countable (A : set R) : is_subset1 A -> countable A.
Proof.
move=> A1.
have[->|] := eqVneq A set0.
  done.
move/set0P/is_subset1_set1/(_ A1) ->.
exact: countable1.
Qed.

Lemma is_subset1_isolated (r : R) : isolated [set r] = [set r].
Proof.
apply/seteqP; split; first exact: isolatedS.
move=> _/= ->; split => /=.
  by rewrite inE.
exists (ball r 1) => //.
  exact: nbhsx_ballx.
rewrite setIidr// => _ ->.
exact: ballxx.
Qed.

Lemma perfect_set1 (r : R) : ~ perfect_set [set r].
Proof.
move/perfectP => -[_].
rewrite is_subset1_isolated.
move=> /eqP; apply/negP/set0P.
by exists r.
Qed.

Lemma omega_max0 (a b : R) f : omega_max a b f [:: b] = oscillation f `[a, b].
Proof. by rewrite/omega_max/= big_nat1. Qed.

Lemma nondecreasing_total_variation (a b : R) (f : R -> R) :
bounded_variation a b f ->
let H := fun x => fine (total_variation a ^~ f x) in
 {in `[a, b] &, nondecreasing_fun H}.
Proof.
move=> bvf H x y xab yab xy.
have axyf := @total_variation_nondecreasing R a b f _ _ xab yab xy.
rewrite /H fine_le//.
- apply/bounded_variationP => //.
    by move: xab; rewrite in_itv/= => /andP[].
  move: xab; rewrite in_itv/= => /andP[? ?].
by move: bvf; apply: bounded_variationl.
- apply/bounded_variationP => //.
    by move: yab; rewrite in_itv/= => /andP[].
  move: yab; rewrite in_itv/= => /andP[? ?].
  by move: bvf; apply: bounded_variationl.
Qed.

Lemma mesh_mem_filter (a b c d : R) (s : seq R) :
  a <= c -> d <= b ->
  mesh c d [seq x <- s | x \in `[c, d]] <= mesh a b s.
Proof.
Abort.

Lemma mesh_filter (a b : R) (s : seq R) (P : pred R) :
  mesh a b [seq x <- s | P x] <= mesh a b s.
Proof.
Abort.

Lemma closureN (A : set R) r : closure (-%R @` A) (- r) <-> closure A r.
Proof.
split.
- rewrite /closure/= => rA B rB.
  have /rA : nbhs (- r) (-%R @` B) by rewrite nbhsNimage/=; exists B.
  move=> [_/= [[xA Ax <-]]] [y By /eqP]; rewrite eqr_opp => /eqP ?; subst y.
  by exists xA.
- rewrite /closure/= => rA B rB.
  have /rA : nbhs r (-%R @` B).
    by move: rB; rewrite nbhsNimage/= => -[C rC <-]; rewrite setNK.
  move=> [x [Ax/= [y By]]] ?; subst x.
  exists y; split => //=.
  by exists (- y) => //; rewrite opprK.
Qed.

(* TODO: PR *)
Lemma closure_inf (A : set R) : A !=set0 -> has_lbound A -> closure A (inf A).
Proof.
move=> /nonemptyN A0 /has_lb_ubN lbndA.
have /closureN := closure_sup A0 lbndA.
by rewrite -/(inf A) setNK.
Qed.

Lemma compact_Rhull (Z : set R) : compact Z -> Z !=set0 -> Rhull Z = `[inf Z, sup Z].
Proof.
rewrite Rcompact_boundE/= => -[closedZ ubndZ lbndZ] Z0.
rewrite /Rhull !(introT (@asboolP _) _)//.
- rewrite {1}((closure_id _).1 closedZ).
  exact: closure_sup.
- rewrite {1}((closure_id _).1 closedZ).
  by apply: closure_inf.
Qed.

Lemma lebesgue_measure_gt0 (P : set R) :
  compact P -> is_interval P -> P !=set0 -> ~ is_subset1 P ->
  (0 < lebesgue_measure P)%E.
Proof.
rewrite Rcompact_boundE => /= -[closedP ubndP lbndP].
move/is_intervalP => PE P0 P1.
rewrite PE compact_Rhull//; last by rewrite Rcompact_boundE.
rewrite lebesgue_measure_itv/= lte_fin -EFinD.
rewrite has_bound_not_subset1_inf_sup//.
by rewrite lte_fin subr_gt0 has_bound_not_subset1_inf_sup.
Qed.

(* deprecating sorted_map *)
Lemma sort_sorted_fst {T1 T2 : eqType} (le1 : rel T1)
  (p : seq (T1 * T2)) :
  transitive le1 ->
  let le12 := (fun x y : T1 * T2 => le1 x.1 y.1) in
  sorted le12 p <-> sorted le1 [seq i.1 | i <- p].
Proof.
Abort.

Lemma sort_sorted_fst_iota (p : seq (R * R)) n :
  let le1 := (fun x y : R * R => x.1 <= y.1) in
  sorted le1 p ->
  size p = n ->
  sorted <=%R [seq (p`_i).1 | i <- iota 0 n].
Proof.
move=> le1 le1p pn.
rewrite (map_comp fst).
rewrite sorted_map.
rewrite -/lt1 -pn.
by rewrite map_nth_iota ?subn0// drop0 take_size.
Qed.

(* map_rcons *)
Lemma rcons_fst {T : Type} (s : seq (T * T)) (x : T * T) :
  unzip1 (rcons s x) = rcons (unzip1 s) x.1.
Proof.
by move: s x; elim => // s1 s2 + s3/= => ->.
Abort.

(* duplicate map_rcons *)
Lemma rcons_snd {T : Type} (s : seq (T * T)) (x : T * T) :
  unzip2 (rcons s x) = rcons (unzip2 s) x.2.
Proof.
by move: s x; elim => // s1 s2 + s3/= => ->.
Abort.

(* duplicate map_rcons *)
Lemma rcons_snd_iota {T : nzSemiRingType} (s : seq (T * T)) (x : T * T) m :
  [seq ((rcons s x)`_i).2 | i <- iota 0 m.+1] =
  rcons [seq (s`_i).2 | i <- iota 0 m] (x.2).
Proof.
Abort.

(* duplicate map_rcons *)
Lemma sort_sorted_snd' (p : seq (R * R)) n :
  let le1 := (fun x y : R * R => x.1 <= y.1) in
  size p = n.+1 ->
  sorted le1 p ->
  (forall i, (p`_i).1 < (p`_i).2) ->
  ((forall i j, `](p`_i).1, (p`_i).2[ `&` `](p`_j).1, (p`_j).2[ = set0) ->
    sorted <=%R [seq (p`_i).2 | i <- iota 0 n.+1] /\
      (forall i, (i < n)%N -> (p`_i).2 <= (p`_i.+1).1)).
Proof.
move=> le1.
move: p; elim: n => // m IHn.
apply: last_ind => // p1 p2 _.
rewrite size_rcons; move/eq_add_S.
move=> pn sp ltp disjp.
have p21m : ((rcons p1 p2)`_m).2 <= ((rcons p1 p2)`_m.+1).1.
  admit.
split.
Abort.

Lemma setD_bigcup_itvoo (c d : R) (a_ b_ : R^nat) n :
  (forall i, (i < n.+1)%N -> a_ i \in `[c, d]) ->
  (forall i, (i < n.+1)%N -> b_ i \in `[c, d]) ->
  sorted <=%R [seq a_ i | i <- iota 0 n.+1] ->
  sorted <=%R [seq b_ i | i <- iota 0 n.+1] ->
  (forall i, (i < n)%N -> b_ i <= a_ i.+1) ->
  `[c, d] `\` \big[setU/set0]_(i < n.+1) `]a_ i, b_ i[%classic =
  `[c, a_ 0]  `|`
  \big[setU/set0]_(i < n) `[b_ i, a_ i.+1]%classic `|`
  `[b_ n, d].
Proof.
elim: n c d a_ b_ => [c d a_ b_ acd bcd sorteda sortedb blea|].
  rewrite big_ord0 setU0 big_ord_recl/= big_ord0 setU0.
  rewrite setDE setCitv/= setIUr; congr setU.
  - rewrite -itv_setI/=.
    rewrite /Order.meet/=.
    rewrite meet_r ?bnd_simp//.
    by rewrite (itvP (acd 0 _)).
  - rewrite -itv_setI/=.
    rewrite /Order.meet/=.
    rewrite meet_l//.
    rewrite join_r ?bnd_simp//.
    by rewrite (itvP (bcd 0 _)).
move=> n ih c d a_ b_ acd bcd sorteda sortedb blea.
rewrite big_ord_recr/=.
rewrite setDE.
rewrite setCU.
rewrite setIA.
rewrite setIAC.
rewrite (_ : `[c, d] `&` _ = `[c, a_ n.+1] `|` `[b_ n.+1, d]); last first.
  rewrite setCitv//= setIUr.
  rewrite -!itv_setI/=.
  rewrite /Order.meet/=.
  rewrite meet_r ?bnd_simp//; last first.
    by rewrite (itvP (acd _ _)).
  rewrite join_l//.
  rewrite meet_l ?bnd_simp//.
  rewrite join_r// bnd_simp.
  by rewrite (itvP (bcd _ _)).
rewrite setIUl.
rewrite -setDE.
rewrite ih//; last 5 first.
- move=> i ni.
  rewrite in_itv/=.
  rewrite (itvP (acd _ _))/=; last by rewrite (ltn_trans ni).
  have := sorted_leq_nth le_trans lexx 0 sorteda i n.+1.
  rewrite !inE !size_map size_iota.
  move=> /(_ (ltnW ni) ltac:(by []) (ltnW ni)).
  rewrite (nth_map 0) ?size_iota; last exact: ltnW.
  rewrite nth_iota//; last exact: ltnW.
  by rewrite (nth_map 0) ?size_iota// nth_iota//.
- move=> i ni.
  rewrite in_itv/=.
  rewrite (itvP (bcd _ _))/=; last by rewrite ltnS ltnW.
  rewrite (le_trans (blea i _))//.
  have [->//|] := eqVneq i n.
  rewrite eq_le negb_and -!ltNge => /orP[|].
    rewrite ltEnat/= => ltni.
    have := leq_trans ni ltni.
    by rewrite ltnn.
  rewrite ltEnat/= => ltni.
  have := sorted_leq_nth le_trans lexx 0 sorteda i.+1 n.+1.
  rewrite !inE !size_map size_iota.
  move=> /(_ (ltnSE ni) ltac:(by []) ni).
  rewrite (nth_map 0) ?size_iota; last exact: ltnW.
  rewrite nth_iota//.
  by rewrite (nth_map 0) ?size_iota// nth_iota//.
- apply: subseq_sorted sorteda.
    exact: le_trans.
  apply: map_subseq.
  rewrite -(addn1 n.+1).
  rewrite iotaD.
  exact: prefix_subseq.
- apply: subseq_sorted sortedb.
    exact: le_trans.
  apply: map_subseq.
  rewrite -(addn1 n.+1).
  rewrite iotaD.
  exact: prefix_subseq.
- move=> k kn.
  apply: blea.
  by rewrite ltnS ltnW.
rewrite [in RHS]big_ord_recr/=.
rewrite -!setUA.
congr setU.
congr setU.
congr setU.
rewrite setIidl//.
apply: subsetCr.
rewrite -[X in X `<=` _](bigcup_mkord _ (fun i => `]a_ i, b_ i[%classic)).
move=> r [i ni/= rab].
rewrite in_itv/=.
apply/negP; rewrite negb_and; apply/orP; left.
rewrite -ltNge.
rewrite (@lt_le_trans _ _ (b_ i))//.
  by rewrite (itvP rab).
have := sorted_leq_nth le_trans lexx 0 sortedb i n.+1.
rewrite !inE !size_map size_iota.
move=> /(_ (ltnW ni) ltac:(by []) (ltnW ni)).
rewrite !(nth_map 0) ?size_iota//; last exact: ltnW.
by rewrite !nth_iota//; last exact: ltnW.
Qed.

(* duplicate get_subset1? *)
Lemma is_subset1_set1 (A : set R) :
  A !=set0 -> is_subset1 A -> exists x, A = [set x].
Proof.
move=> [x Ax] A1; exists x; apply/seteqP; split => [|y ->//].
by move=> y Ay; exact: A1.
Abort.

Lemma set1_not_open (x : R) : ~ open [set x].
Proof. by rewrite openE/= interior_set1 => /(_ x); exact. Qed.

(* duplicate nth_map? *)
Lemma snd_map {T1 T2} (l : seq (T1 * T2)) d1 d2 i :
 (i < size l)%N ->
  (nth (d1, d2) l i).2 = nth d2 (map snd l) i.
Proof. by move=> ?; rewrite (nth_map (d1, d2)). Qed.

(* duplicate nth_map? *)
Lemma fst_map {T1 T2} (l : seq (T1 * T2)) d1 d2 i :
   (i < size l)%N ->
  (nth (d1, d2) l i).1 = nth d1 (map fst l) i.
Proof. by move=> ?; rewrite (nth_map (d1, d2)). Qed.

(* *)
Lemma nth_set (P : set R) (l : seq R) i : (i < size l)%N ->
  [set` l] `<=` P -> P (nth 0 l i).
Proof.
move=> li lA.
by have /lA := mem_nth 0 li.
Abort.

End lemmas.

Section contiguous_intervals_lemmas.
Context {R : realType}.

Lemma contiguous_intervals2_notin' (Z : set R) j l : compact Z ->
  contiguous_intervals Z j !=set0 ->
  j != l ->
  ((contiguous_intervals2 Z j))
    \notin `]contiguous_intervals1 Z l, contiguous_intervals2 Z l[.
Proof.
move=> /[dup] cZ; rewrite Rcompact_boundE/= => -[closeZ uZ lZ] Zj0 j_neq_l.
rewrite in_itv/=.
rewrite negb_and -[X in _ || X]leNgt -implybE; apply/implyP.
rewrite fine_contiguous_intervals2// fine_contiguous_intervals1// => lj.
rewrite !fine_contiguous_intervals2//.
rewrite leNgt; apply/negP => jl.
have H : contiguous_intervals Z j `&` contiguous_intervals Z l = set0.
  have /trivIsetP := @disjoint_contiguous_intervals _ Z.
  exact.
move: (H).
apply/eqP/set0P.
have ? : inf (contiguous_intervals Z j) < sup (contiguous_intervals Z j).
  apply: has_bound_not_subset1_inf_sup.
  exact: has_lbound_contiguous_intervals.
  exact: has_ubound_contiguous_intervals.
  move/is_subset1_set1 => /(_ Zj0)Zj1.
  have := @open_contiguous_intervals _ Z j.
  by rewrite Zj1; exact: set1_not_open.
have H1 : inf (contiguous_intervals Z j) < inf (contiguous_intervals Z l).
  rewrite ltNge; apply/negP => lj'.
  move: H.
  apply/eqP/set0P.
  pose m := (inf (contiguous_intervals Z j) + sup (contiguous_intervals Z j)) / 2.
  exists m; split.
    rewrite contiguous_ooitv//= in_itv/=.
    rewrite fine_contiguous_intervals1//.
    rewrite fine_contiguous_intervals2//.
    by rewrite !midf_lt//=.
  rewrite contiguous_ooitv//= in_itv/=.
  rewrite fine_contiguous_intervals1//.
  rewrite fine_contiguous_intervals2//.
  apply/andP; split.
    rewrite /m.
    by rewrite (le_lt_trans lj')// midf_lt.
  rewrite (le_lt_trans _ jl)// midf_le//.
  exact/ltW.
pose m : R := (inf (contiguous_intervals Z l) + sup (contiguous_intervals Z j)) / 2.
exists m; split.
  rewrite contiguous_ooitv//= in_itv/=.
  rewrite fine_contiguous_intervals1//.
  rewrite fine_contiguous_intervals2//.
  rewrite !midf_lt// andbT.
  rewrite /m.
  rewrite (lt_le_trans H1)//.
  by rewrite midf_le// ltW.
rewrite contiguous_ooitv//= in_itv/=.
rewrite fine_contiguous_intervals1//.
rewrite  fine_contiguous_intervals2//.
rewrite !midf_lt//=.
rewrite (le_lt_trans _ jl)// midf_le//.
exact: ltW.
Qed.

Lemma contiguous_intervals1_notin' (Z : set R) j l : compact Z ->
  contiguous_intervals Z j !=set0 ->
  j != l ->
  ((contiguous_intervals1 Z j))
    \notin `]contiguous_intervals1 Z l, contiguous_intervals2 Z l[.
Proof.
move=> /[dup] cZ; rewrite Rcompact_boundE/= => -[closeZ uZ lZ] Zj0 j_neq_l.
rewrite in_itv//=.
rewrite negb_and -[X in _ || X]leNgt -implybE; apply/implyP.
rewrite fine_contiguous_intervals1// fine_contiguous_intervals1// => lj.
rewrite leNgt; apply/negP => jl.
have H : contiguous_intervals Z j `&` contiguous_intervals Z l = set0.
  have /trivIsetP := @disjoint_contiguous_intervals _ Z.
  exact.
move: (H).
apply/eqP/set0P.
have ? : inf (contiguous_intervals Z j) < sup (contiguous_intervals Z j).
  apply: has_bound_not_subset1_inf_sup.
  exact: has_lbound_contiguous_intervals.
  exact: has_ubound_contiguous_intervals.
  move/is_subset1_set1 => /(_ Zj0)Zj1.
  have := @open_contiguous_intervals _ Z j.
  by rewrite Zj1; exact: set1_not_open.
have H1 : sup (contiguous_intervals Z l) < sup (contiguous_intervals Z j).
  rewrite ltNge; apply/negP => lj'.
  move: H.
  apply/eqP/set0P.
  pose m := (inf (contiguous_intervals Z j) + sup (contiguous_intervals Z j)) / 2.
  exists m; split.
    rewrite contiguous_ooitv//= in_itv/=.
    rewrite fine_contiguous_intervals1//.
    rewrite fine_contiguous_intervals2//.
    by rewrite !midf_lt//=.
  rewrite contiguous_ooitv//= in_itv/=.
  rewrite fine_contiguous_intervals1//.
  rewrite fine_contiguous_intervals2//.
  apply/andP; split.
    rewrite /m.
    rewrite (lt_le_trans lj)// midf_le//.
    exact/ltW.
  rewrite /m.
  by rewrite (lt_le_trans _ lj')// midf_lt//.
pose m : R := (inf (contiguous_intervals Z j) + sup (contiguous_intervals Z l)) / 2.
exists m; split.
  rewrite contiguous_ooitv//= in_itv/=.
  rewrite fine_contiguous_intervals1//.
  rewrite fine_contiguous_intervals2//.
  rewrite !midf_lt//=.
  rewrite /m.
  rewrite (le_lt_trans _ H1)//.
  by rewrite midf_le// ltW.
rewrite contiguous_ooitv//= in_itv/=.
rewrite fine_contiguous_intervals1//.
rewrite fine_contiguous_intervals2//.
rewrite !midf_lt//= andbT.
rewrite /m.
rewrite (lt_le_trans lj)// midf_le//.
exact: ltW.
Qed.

Lemma contiguous_intervals2_notin (Z : set R) : has_ubound Z -> forall j,
  ((contiguous_intervals2 Z j))
    \notin `]contiguous_intervals1 Z j, contiguous_intervals2 Z j[.
Proof.
move=> ubZ j.
rewrite in_itv/=.
by rewrite ltxx andbF.
Qed.

Lemma contiguous_intervals1_notin (Z : set R) : has_lbound Z -> forall j,
  ((contiguous_intervals1 Z j))
    \notin `]contiguous_intervals1 Z j, contiguous_intervals2 Z j[.
Proof.
move=> lbZ j.
rewrite in_itv/=.
by rewrite ltxx/=.
Qed.

Lemma mem_contiguous_intervals2 (Z : set R) j :
  compact Z ->
  Z !=set0 ->
  contiguous_intervals Z j !=set0 ->
  Z ((contiguous_intervals2 Z j)).
Proof.
move=> cZ Z0 Zj0.
move: (cZ); rewrite Rcompact_boundE/= => -[closedZ ubndZ lbndZ].
have cpltZE := bigcup_contiguous_intervals closedZ.
have H1 : (cplt_hull Z) =
    \bigcup_k `]contiguous_intervals1 Z k, contiguous_intervals2 Z k[%classic.
  rewrite [in LHS]cpltZE; apply: eq_bigcup => // i _.
  by rewrite contiguous_ooitv.
have : (~` (cplt_hull Z)) (sup (contiguous_intervals Z j)).
  move=> H2.
  have : ((cplt_hull Z)) (sup (contiguous_intervals Z j)).
    by [].
  rewrite H1 => -[l _].
  apply/negP.
  rewrite -fine_contiguous_intervals2//.
  have [->{l}|ij] := eqVneq l j.
    exact: contiguous_intervals2_notin.
  apply: contiguous_intervals2_notin' => //.
  by rewrite eq_sym.
rewrite fine_contiguous_intervals2//.
rewrite /cplt_hull setCD => -[/=|//].
have : sup (contiguous_intervals Z j) \in [set` Rhull Z].
  have H3 : (closure (contiguous_intervals Z j)) (sup (contiguous_intervals Z j)).
    apply: closure_sup => //.
    exact: has_ubound_contiguous_intervals.
  have H4 : closure (contiguous_intervals Z j) `<=` [set` Rhull Z].
    rewrite [X in _ `<=` X](closure_id _).1//; last first.
      rewrite compact_Rhull//.
      exact: itv_closed_ends_closed.
    apply: (@subset_trans _ (closure (cplt_hull Z))).
      rewrite cpltZE.
      apply: closureS.
      by apply: bigcup_sup.
    apply: closureS.
    by apply: cplt_hull_subset_Rhull.
  have := H4 _ H3.
  by rewrite /= inE.
by rewrite inE  =>  ->.
Qed.

Lemma mem_contiguous_intervals1 (Z : set R) j :
  compact Z ->
  Z !=set0 ->
  contiguous_intervals Z j !=set0 ->
  Z ((contiguous_intervals1 Z j)).
Proof.
move=> cZ Z0 Zj0.
move: (cZ); rewrite Rcompact_boundE/= => -[closedZ ubndZ lbndZ].
have cpltZE := bigcup_contiguous_intervals closedZ.
have H1 : (cplt_hull Z) =
    \bigcup_k `]contiguous_intervals1 Z k, contiguous_intervals2 Z k[%classic.
  rewrite [in LHS]cpltZE; apply: eq_bigcup => // i _.
  by rewrite contiguous_ooitv.
have : (~` (cplt_hull Z)) (inf (contiguous_intervals Z j)).
  move=> H2.
  have : ((cplt_hull Z)) (inf (contiguous_intervals Z j)).
    by [].
  rewrite H1 => -[l _].
  apply/negP.
  rewrite -fine_contiguous_intervals1//.
  have [->{l}|ij] := eqVneq l j.
    exact: contiguous_intervals1_notin.
  apply: contiguous_intervals1_notin' => //.
  by rewrite eq_sym.
rewrite fine_contiguous_intervals1//.
rewrite /cplt_hull setCD => -[/=|//].
have : inf (contiguous_intervals Z j) \in [set` Rhull Z].
  have H3 : (closure (contiguous_intervals Z j)) (inf (contiguous_intervals Z j)).
    apply: closure_inf => //.
    exact: has_lbound_contiguous_intervals.
  have H4 : closure (contiguous_intervals Z j) `<=` [set` Rhull Z].
    rewrite [X in _ `<=` X](closure_id _).1//; last first.
      rewrite compact_Rhull//.
      exact: itv_closed_ends_closed.
    apply: (@subset_trans _ (closure (cplt_hull Z))).
      rewrite cpltZE.
      apply: closureS.
      by apply: bigcup_sup.
    apply: closureS.
    by apply: cplt_hull_subset_Rhull.
  have := H4 _ H3.
  by rewrite /= inE.
by rewrite inE  =>  ->.
Qed.

End contiguous_intervals_lemmas.

Section preliminaries.
Context {R : realType}.

Lemma nth_map_iota {T} (x : T) (n : nat) (f : nat -> T) (i : nat) :
  (i < n)%N ->
  nth x [seq f k | k <- iota 0 n] i = f i.
Proof.
by move=> iltn; rewrite (nth_map 0%N) ?nth_iota; last by rewrite size_iota.
Qed.

Lemma nth_cons_map_iota (x y : R) (n : nat) (f : nat -> R) (i : nat) :
  (i < n.+1)%N ->
  nth x (y :: [seq f k | k <- iota 0 n]) i = if i == 0 then y else f i.
Proof.
Abort.

Definition lambda_partition (a b : R) (lambda : R) :=
  let n := (truncn ((b - a) / lambda)).+1 in
  [seq (a + (b - a) * i.+1%:R / n%:R) | i <- iota 0 n].

Local Notation lp := lambda_partition.

Lemma lambda_partition_size0_tmp (a b l : R) :
  (0 < (truncn ((b - a) / l)).+1)%N.
Proof. by []. Qed.

Lemma lambda_partition_size0 (a b l : R) :
  a < b -> 0 < l ->
  (0 < size (lp a b l))%N.
Proof.
move=> ab l0; by rewrite size_map size_iota lambda_partition_size0_tmp.
Qed.

Lemma lambda_partition_div_width (a b l : R) (i : nat) :
  a < b -> 0 < l ->
  `|nth b (a :: (lp a b l)) i.+1 - nth b (a :: (lp a b l)) i| < l.
Proof.
move=> ab l0.
have lpw0 := lambda_partition_size0_tmp.
case: i.
  rewrite /= mulr1 -addrA subrKC.
  rewrite gtr0_norm; last by rewrite divr_gt0// subr_gt0.
  rewrite ltr_pdivrMr// mulrC -ltr_pdivrMr//.
  exact: truncnS_gt.
move=> n.
have [|] := leqP n (truncn ((b - a) / l)).
  rewrite leq_eqVlt => /predU1P[-> |].
    rewrite nth_default; last by rewrite /= size_map size_iota.
    rewrite [lp a b l]lock /=; unlock; rewrite nth_map_iota//.
    by rewrite -mulrA divff// mulr1 subrKC subrr normr0.
  admit.
move=> nsize.
rewrite 2?nth_default ?subrr ?normr0//.
Abort.

Lemma lambda_partition_partition (a b l : R) :
  a < b -> 0 < l ->
  itv_partition a b (lp a b l).
Proof.
move=> ab l0.
split; last first.
- rewrite (last_nth b).
  rewrite -(@prednK (size _))/=; last exact: lambda_partition_size0.
  rewrite nth_map_iota//.
  rewrite size_map size_iota mulfK; first by rewrite subrKC.
  rewrite lt0r_neq0//.
- admit.
Abort.

Lemma lambda_mesh (a b l : R) :
  a < b -> 0 < l ->
  mesh a b (lp a b l) < l.
Proof.
move=> ab l0.
rewrite /mesh -bigmaxr_morph.
apply: bigmax_lt => // n _.
(*exact: lambda_partition_div_width.*)
Abort.

End preliminaries.

Section limit_point_closed.
Context {R : realType}.

Lemma not_limit_point_set1 (A : set R) (a : R) : ~ limit_point A a ->
  exists e : {posnum R}, ball a e%:num `&` A `<=` [set a].
Proof.
move=> Ua; apply/not_existsP => aAa.
apply: Ua; rewrite /limit_point => /= V [e /= e0 aeV].
have /nonsubset[/= x [[aex Ax] /eqP xa]] := aAa (PosNum e0).
by exists x; split => //; exact: aeV.
Qed.

Lemma limit_point_closed (A : set R) : closed (limit_point A).
Proof.
rewrite -openC.
set U : set R := ~` _.
rewrite openE/= => a /not_limit_point_set1[e AeAa].
rewrite /interior /nbhs/= /nbhs_ball_; exists e%:num => //= b bae.
suff : b \notin limit_point A by rewrite notin_setE.
have [{}bae aeEa] : nbhs b (ball a e%:num) /\ ball a e%:num `&` A `<=` [set a].
  have [ab|ab] := eqVneq a b.
    split=> [|/= r [aer Ar]].
      by rewrite ab; exact: nbhsx_ballx.
    exact: AeAa.
  split => //.
  rewrite /nbhs/= /nbhs_ball_/=.
  exists (Num.min `|b - a| (e%:num - `|b - a|)) => //=.
    by rewrite lt_min/= normr_gt0 subr_eq0 eq_sym ab/= subr_gt0 distrC.
  move=> x.
  rewrite /ball /ball_ /= lt_min => /andP[bxba bxe].
  by rewrite -(subrKA b) (le_lt_trans (ler_normD _ _))// -ltrBrDl (distrC a).
rewrite notin_setE => /limit_point_infinite_setP/(_ _ bae); apply.
exact: (sub_finite_set aeEa).
Qed.

Section checking.

Lemma isolated_id_set1 (x : R) : isolated [set x] = [set x].
Proof.
rewrite eqEsubset; split; first exact: isolatedS.
rewrite -[isolated _]setU0.
apply: (subset_trans (@subset_closure _ _)).
rewrite closure_isolated_limit_point.
apply: setUS.
move=> z.
move/limit_pointP => [z_ [zx nzx cvgz]]/=.
have := zx z.
have rzx : range z_ x by exists 0 => //; apply: zx.
apply/not_implyP; split => //.
Abort.

Lemma isolated_points_of_limit_points_is_not_empty :
  exists A : set R, isolated (limit_point A) !=set0.
Proof.
exists [set n.+1%:R^-1 | n in [set: nat]].
exists 0%:R; split.
  rewrite inE.
  apply/limit_pointP.
  exists (fun n => n.+1%:R^-1); split.
  - done.
  - move=> n.
    by rewrite lt0r_neq0.
  - have <- : inf [set n.+1%:R^-1 | n in [set: nat]] = 0%:R :> R.
      apply/eqP; rewrite eq_le; apply/andP; split; last first.
        apply: lb_le_inf.
          by exists 1; exists 0 => //; rewrite invr1.
        by move=> _ [n _ <-]; rewrite invr_ge0.
      rewrite -lee_fin.
      rewrite -ereal_inf_EFin; last 2 first.
      - by exists 0 => _ [n _ <-]; rewrite invr_ge0.
      - by exists 1; exists 0 => //; rewrite invr1.
        have : {homo (fun n : nat => (n.+1%:R^-1)%:E : \bar R) :
                                     n m / (n <= m)%N >-> (m <= n)%E}.
          apply/nonincreasing_seqP => n.
          rewrite lee_fin.
          rewrite lef_pV2 ?posrE//.
          by rewrite ler_nat.
        rewrite image_comp.
        move/ereal_nonincreasing_cvgn/cvg_lim <- => //.
        rewrite le_eqVlt; apply/predU1P; left.
        apply: cvg_lim => //.
        apply/cvg_EFin.
          by apply: nearW => n.
        exact: cvg_harmonic.
    apply: nonincreasing_cvgn.
      apply/nonincreasing_seqP => n.
      by rewrite lef_pV2 ?posrE// ler_nat.
    by exists 0%:R => _ [n _ <-]; rewrite invr_ge0 (_ : 0 = 0%:R)// ler_nat.
exists (ball 0 1).
  exact: nbhsx_ballx.
rewrite eqEsubset; split.
  move=> x/= [] _ l2.
  apply/not_notP => /eqP.
  rewrite eq_le.
  rewrite negb_and => /orP.
  rewrite -2!ltNge => -[]x0;move/limit_point_infinite_setP : l2; apply/existsNP.
    have [x1|x1] := leP 1 x.
      exists (ball x (x - 1 / 2)).
      apply/not_implyP; split.
        apply: nbhsx_ballx.
        rewrite subr_gt0.
        apply: lt_le_trans _ x1.
        rewrite div1r invf_lt1//.
        by rewrite (_ : 1 = 1%:R)// ltr_nat.
      rewrite not_notP.
      apply/finite_set_leP.
      exists 1.
      rewrite -(card_le_eqr (@card_set1 R 1%:R)).
      apply: subset_card_le.
      move=> r/= [+ [n _]];  move/[swap] => <-{r}.
      apply: contraPP.
      case: n => // n _; first by rewrite invr1 in n.
      apply/negP; rewrite /ball/= -leNgt.
      rewrite ler_normr; apply/orP; left.
      rewrite lerB//.
      rewrite ler_pdivlMr//.
(*      rewrite exprSr divfK//.
      apply: exprn_ile1 => //.
      rewrite invf_le1//.
      by rewrite (_ : 1 = 1%:R)// ler_nat.
    exists (ball x (x / 2)).
    apply/not_implyP; split.
      apply: nbhsx_ballx.
      by rewrite divr_gt0.
    rewrite not_notE.
    apply/finite_set_leP.
    exists (truncn (x / 2)).+1.
    apply: (@card_le_trans _ _ _
           [set n%:R | n in `I_((Nat.log2 (truncn (x / 2))).+1)]).
      apply: subset_card_le.
      move=> r/=[+ [n _]] => /[swap] => <-{r}.
      rewrite /ball/=.
      move/ltr_normlW; rewrite ltrBlDr -ltrBlDl {1}(splitr x) addrK => x2n.
      exists (Nat.log2 (truncn (x / 2))) => //.
      rewrite 
      rewrite -{2}(invrK 2) -{2}(expr1 2^-1).
      
      rewrite gtr0_norm; last first.
        rewrite 
  move/limit_pointP => [a_ [a2]].
rewrite subset_set1.
*)
Abort.

Lemma perfect_set_closedDisolated (A : set R) : closed A ->
  perfect_set (A `\` isolated A).
Proof.
(*
move=> cA.
split.
*)
Abort.

End checking.

End limit_point_closed.
Arguments limit_point_closed {R} A.

(* TODO: PR *)
Section interior_lemmas.
Context {R : realType}.

Lemma isolated_interior_set0 (A : set R) :
  isolated (interior A) = set0.
Proof.
apply/eqP.
apply: contrapT.
move/negP.
move/set0P.
move=> [/= x [Ax /=[V]]].
rewrite nbhsE/=.
move=> [U [oU Ux] UV] => VAx.
have {V UV VAx}UAx : U `&` (interior A) = [set x].
  rewrite eqEsubset; split.
    rewrite -VAx.
    exact: setSI.
  rewrite sub1set inE; split => //.
  by rewrite inE in Ax.
have : open (U `&` (interior A)).
  apply: openI => //.
  exact: open_interior.
rewrite UAx.
move/(interior_id _).1.
rewrite interior_set1.
by rewrite eqEsubset => -[_ /(_ x erefl)].
Qed.

Lemma nonempty_open_interval_not_subset1 (A : set R) :
  A !=set0 -> open A -> is_interval A ->
  ~ is_subset1 A.
Proof.
move=> [x Ax] oA itvA.
apply/existsNP.
have /(_ x Ax)[e/= e0] := open_subball oA.
have e20 : 0 < e / 2 by exact: divr_gt0.
move/(_ (e / 2)).
have ballee2 : ball_ [eta normr] 0 e (e / 2).
  rewrite /ball_/= sub0r normrN gtr0_norm//.
by rewrite -subr_gt0 {1}(splitr e) addrK.
move/(_ ballee2 e20).
move/(subset_trans (subset_closure_half e20)).
Abort.

Lemma limit_point_interior (A : set R) :
  interior A `<=` limit_point (interior A).
Proof.
move=> /= x [e /=e0].
rewrite open_subsetE; last exact: ball_open.
 move=> ballxA.
apply/limit_pointP.
exists (fun n => x - e / n.+2%:R); split.
- move=> _/= [n _ <-].
  apply: ballxA; rewrite /ball_/=.
  rewrite opprB addrCA subrr addr0 ger0_norm; last first.
    by rewrite divr_ge0// ltW.
  rewrite ltr_pdivrMr//.
  rewrite ltr_pMr//.
  by rewrite {1}(_ : 1 = 1%:R)// ltr_nat.
- move=> n.
  rewrite neq_lt; apply/orP; left.
  rewrite gtrBl.
  by rewrite divr_gt0.
- rewrite -{2}(subr0 x).
  apply: cvgB.
    exact: cvg_cst.
  rewrite -(mulr0 e).
  apply: cvgM.
    exact: cvg_cst.
  apply/cvgrVy.
    by apply: nearW.
  under eq_cvg do rewrite /unstable.inv_fun/= invrK.
  apply/cvgrnyP.
  rewrite cvg_shiftS.
  rewrite (cvg_shiftS (fun x => x)).
  exact: cvg_id.
Qed.

Lemma ex_perfect_set (A : set R) :
  closed A ->
  exists B, [/\ B `<=` A, perfect_set B &
   (0 < lebesgue_measure A)%E -> (0 < lebesgue_measure B)%E].
Proof.
move=> cA.
exists (closure (interior A)); split.
- rewrite {2}((closure_id _).1 cA).
  apply: closureS.
  exact: interior_subset.
- apply/perfectP; split; first exact: closed_closure.
  rewrite closure_isolated_limit_point.
  rewrite isolated_interior_set0 set0U.
  rewrite -subset0.
  move=> /= x []/= .
  rewrite inE; move/[dup] => limAx /limit_pointP[a_ [aA anx cvgax]].
  move=> [V].
  rewrite nbhsE/= => -[U [oU Ux] UV VAx].
  have {V UV VAx}UAx : U `&` limit_point (interior A) = [set x].
    rewrite eqEsubset; split.
      rewrite -VAx.
      exact: setSI.
    by rewrite sub1set inE; split.
  pose I_ := open_disjoint_itv oU.
  have := Ux.
  rewrite (open_disjoint_itv_bigcup oU) => -[n _ Inx].
  have In0 : I_ n !=set0 by exists x.
(*  have := nonempty_open_interval_not_subset1 In0 (@open_disjoint_itv_open _ _ oU n) (@open_disjoint_itv_is_interval _ _ oU n).
  move/existsNP => [x0 /existsNP[x1] /not_implyP[Inx0] /not_implyP[Inx1]].
  move/eqP.
  rewrite eq_le.
  move/nandP.
  rewrite -2!ltNge => -[x10|x01].*)
Abort.

End interior_lemmas.

Section continuous_interval.
Context {R : realType}.
Variables (D : set R) (f : R -> R).
Hypothesis cf : {within D, continuous f}.

Lemma is_interval_image_cc a b : `[a, b] `<=` D ->
  is_interval (f @` `[a, b]).
Proof.
have [ab abD|ba _] := leP a b; last first.
  rewrite set_itv_ge// ?bnd_simp -?ltNge// image_set0.
  exact/connected_intervalP/connected0.
move=> _ _/= -[x0 x0ab <-] [x1 x1ab <-] z /andP[fx0z zfx1].
have [x01|x10] := leP x0 x1.
  have [x xx01 fxz] : exists2 x : R, x \in `[x0, x1] & f x = z.
    apply: IVT => //.
      apply: continuous_subspaceW cf.
      by apply: subset_trans abD; apply: subset_itv;
        rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
    by rewrite ge_min le_max fx0z/= zfx1 orbT.
  exists x => //.
  by apply: subset_itv xx01; rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
have [x xx01 fxz] : exists2 x : R, x \in `[x1, x0] & f x = z.
  apply: IVT => //.
  - exact: ltW.
  - apply: continuous_subspaceW cf.
    by apply: subset_trans abD; apply: subset_itv;
      rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
  by rewrite ge_min le_max fx0z/= zfx1 orbT.
exists x => //.
by apply: subset_itv xx01; rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
Qed.

End continuous_interval.

Section diam.
Context {R : realType}.

Definition diam (A : set R) :=
  if A == set0 then 0%:E else
  ereal_sup ([set `|a.1 - a.2|%:E | a in setX A A]).

Lemma diam0 : diam set0 = 0%:E.
Proof.
by rewrite /diam eqxx.
Qed.

Lemma diam_ge0 (A : set R) : (0 <= diam A)%E.
Proof.
rewrite /diam; case: ifPn => //.
move/set0P => [x Ax].
apply: le_ereal_sup_tmp.
by exists 0 => //; exists (x, x) => /=; rewrite ?subrr ?normr0//.
Qed.

Lemma diamS (A B : set R) : A `<=` B -> (diam A <= diam B)%E.
Proof.
move=> AB.
rewrite {1}/diam; case : ifPn => [_|].
  exact: diam_ge0.
move/set0P => [a Aa].
rewrite /diam; case: ifPn => [|_].
  move/eqP => B0.
  have := AB a Aa.
  by rewrite B0.
apply: ereal_sup_le => r/= [[x y] [/= Ax Ay] <-].
exists (x, y) => //=.
by split; apply: AB.
Qed.

Lemma diam_Rhull (A : set R) : diam [set` Rhull A] = diam A.
Proof.

Admitted.

Lemma diam_closure (A : set R) : diam (closure A) = diam A.
Proof.
have [->|A0] := eqVneq A set0.
  by rewrite closure0.
rewrite -diam_Rhull -(diam_Rhull A).
Admitted.

Lemma diam_itv (x y: R) (b0 b1 : bool) :
  x <= y ->
  diam [set` (Interval (BSide b0 x) (BSide b1 y))] = (y - x)%:E.
Proof.
Admitted.

Definition diam_max (s : seq (set R)) := \big[maxe/-oo%E]_(A <- s) (diam A).

Lemma diam_max_ge0 (s : seq (set R)) : s != [::] -> (0 <= diam_max s)%E .
Proof.
case: s => // s0 s1 _.
rewrite /diam_max.
apply: (bigmax_sup_seq _ s0) => //.
  exact: mem_head.
exact: diam_ge0.
Qed.

Lemma diam_max_seq1 (s0 : set R) : diam_max [:: s0] = diam s0.
Proof.
by rewrite /diam_max big_seq1.
Qed.

Lemma diam_max_cons (s0 : set R) (s : seq (set R)) :
  (diam s0 <= diam_max (s0 :: s))%E .
Proof.
apply: (bigmax_sup_seq _ s0) => //.
exact: mem_head.
Qed.

(* unnecessary? *)
Lemma diam_defaultE (s : seq (set R)) :
  s != [::] ->
diam_max s = \big[maxe/0%E]_(A <- s) (diam A).
Proof.
elim: s => // s0 s1 ih _.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: le_bigmax_seq2 => /=.
    by exists s0; rewrite ?mem_head ?leNye.
  move=> i.
  rewrite in_cons => /predU1P[->|is1].
    by exists s0 => //; rewrite mem_head.
  exists i => //.
  by rewrite in_cons is1 orbT.
rewrite big_seq_cond.
apply: bigmax_le.
  exact: diam_max_ge0.
move=> /= A; rewrite andbT in_cons => /predU1P[->|s1A].
  exact: diam_max_cons.
rewrite /diam_max.
rewrite big_cons le_max; apply/orP; right.
have : s1 != [::].
  by apply/negP; move/eqP=> s10; rewrite s10 in s1A.
move/ih; rewrite /diam_max => ->.
exact: le_bigmax_seq.
Qed.

Lemma diam_max0 : diam_max [::] = -oo%E.
Proof.
by rewrite /diam_max big_nil.
Qed.

Lemma diam_maxS (s t : seq (set R)) :
 (forall A, A \in s -> exists2 B, B \in t & A `<=` B) ->
  (diam_max s <= diam_max t)%E.
Proof.
elim: s => //[_|/= s0 s1 ih h].
  by rewrite /diam_max big_nil leNye.
rewrite /diam_max.
rewrite big_cons.
rewrite ge_max; apply/andP; split.
  have [t0 t0t st0] := h s0 (mem_head _ _).
  apply: (@le_trans _ _ (diam t0)).
    exact: diamS.
  exact: le_bigmax_seq.
rewrite big_seq_cond.
apply: bigmax_le.
  exact: leNye.
move=> X.
rewrite andbT => s1X.
have := h X.
rewrite in_cons s1X orbT; move/(_ isT).
move=> [Y s1Y XY].
apply: (@le_trans _ _ (diam Y)).
  exact: diamS.
exact: le_bigmax_seq.
Qed.

End diam.

(*
Section oscillation_measure.
Context {R : realType}.

Variable (f : R -> R).
Definition osc_mu (g : R -> R) := (oscillation g).

Lemma osc_mu0 : osc_mu f set0 = 0.
Proof. by rewrite /osc_mu oscillation0. Qed.

Lemma osc_mu_ge0 A : (0 <= osc_mu f A)%E.
Proof. by rewrite oscillation_ge0. Qed.

Lemma le_osc_mu A B : A `<=` B -> (osc_mu f A <= osc_mu f B)%E.
Proof. exact: oscillation_sub. Qed.

(* oscillation_subadditive2? *)
Lemma osc_mu_subadditive2 A B :
   {within A `|` B, continuous f} -> 
   (osc_mu f (A `|` B) <= osc_mu f A + osc_mu f B)%E.
Proof.
move=> cf.
have := derive.EVT_max cf.

Lemma osc_mu_sigma_subadditive : sigma_subadditive (osc_mu f).
Proof.
move=> A.
rewrite seqDU_bigcup_eq.
Admitted.
*)

Section contiguous_intervals_support.
Context {R : realType}.

Definition contiguous_intervals_support (U : set R) : set nat :=
  [set i | contiguous_intervals U i !=set0].

Lemma bigcup_contiguous_intervals_support (P : set R) :
  \bigcup_k contiguous_intervals P k =
  \bigcup_(k in contiguous_intervals_support P) contiguous_intervals P k.
Proof.
rewrite [RHS]bigcup_mkcond.
apply: eq_bigcupr => i _.
case: ifPn => //.
rewrite notin_setE /contiguous_intervals_support/=.
by move/set0P/negP/negPn/eqP.
Qed.

Lemma contiguous_intervals_sort' (P : set R) i j :
  has_lbound P -> has_ubound P ->
  contiguous_intervals P j !=set0 ->
  contiguous_intervals1 P i <= contiguous_intervals1 P j ->
  contiguous_intervals2 P i <= contiguous_intervals2 P j.
Proof.
move=> lbP ubP Pj0 infsupi.
have ? : has_lbound (contiguous_intervals P i).
  exact: has_lbound_contiguous_intervals.
have ? : has_ubound (contiguous_intervals P i).
  exact: has_ubound_contiguous_intervals.
have ? : has_lbound (contiguous_intervals P j).
  exact: has_lbound_contiguous_intervals.
have ? : has_ubound (contiguous_intervals P j).
  exact: has_ubound_contiguous_intervals.
have H1 : (contiguous_intervals1 P i) <= (contiguous_intervals2 P i).
  by rewrite has_bound_inf_sup.
have H2 : (contiguous_intervals1 P j) <= (contiguous_intervals2 P j).
  by rewrite has_bound_inf_sup.
have [->//|ij] := eqVneq i j.
move: H2; rewrite le_eqVlt => /predU1P[H2|H2].
  move: Pj0.
  by rewrite contiguous_ooitv// H2 set_itv_ge ?bnd_simp// => -[].
rewrite leNgt; apply/negP => abs.
have /trivIsetP/(_ i j Logic.I Logic.I ij) := @disjoint_contiguous_intervals _ P.
pose x := ((contiguous_intervals1 P j + contiguous_intervals2 P j))/2.
rewrite -subset0.
move=> /(_ x)[].
split.
  rewrite contiguous_ooitv//= in_itv/= /x.
  apply/andP; split.
    rewrite (le_lt_trans infsupi)//.
    by rewrite midf_lt//.
  rewrite (le_lt_trans _ abs)//.
  by rewrite midf_le// ltW.
rewrite contiguous_ooitv//= in_itv/= /x.
apply/andP; split.
  by rewrite midf_lt//.
by rewrite midf_lt.
Qed.

Lemma contiguous_intervals_sort (P : set R) p :
  has_lbound P -> has_ubound P ->
  [set` p] `<=` contiguous_intervals_support P ->
  sorted <=%R [seq contiguous_intervals1 P j | j <- p] ->
  sorted <=%R [seq contiguous_intervals2 P j | j <- p].
Proof.
case: p => // h t lbP ubP Pp sorted1.
apply/(sortedP 0) => i.
rewrite size_map [in X in X -> _]/= ltnS => ti.
rewrite (nth_map 0)//; last by rewrite /= ltnW.
rewrite (nth_map 0)//.
apply: contiguous_intervals_sort' => //.
  move: Pp => /(_ t`_i)/=.
  rewrite /contiguous_intervals_support/=.
  apply.
  rewrite inE; apply/orP; right.
  apply/(nthP 0).
  by exists i.
move/(sortedP 0) : sorted1 => /(_ i).
rewrite size_map [in X in (X -> _) -> _]/= ltnS => /(_ ti).
rewrite (nth_map 0)//.
  by rewrite (nth_map 0)//.
by rewrite /= ltnS ltnW.
Qed.

Lemma contiguous_infinite (a b : R) (P : set R) :
  P `<=` `[a, b] ->
  compact P ->
  P !=set0 ->
  lebesgue_measure P = 0 ->
  perfect_set P ->
  infinite_set (contiguous_intervals_support P).
Proof.
move=> Pab compactP P0 muP perfectP.
have closedP : closed P by case: perfectP.
pose U := cplt_hull P.
have openU : open U by apply: closed_open_cplt_hull.
have UE := open_disjoint_itv_bigcup openU.
move=> /finite_seqP_new[/= p up Pp].
have [p0|p0] := eqVneq p [::].
  have : contiguous_intervals_support P = set0.
    by rewrite Pp p0 -subset0 => x/=; rewrite inE.
  have := bigcup_contiguous_intervals closedP.
  rewrite -/U bigcup_contiguous_intervals_support.
  rewrite Pp p0 bigcup0// setD_eq0 => {}Pp _.
  have {}Pp : P = [set` Rhull P] by apply/seteqP; split => //; exact: sub_Rhull.
  move/is_intervalP : Pp => itv_P.
  have : ~ is_subset1 P.
    move/is_subset1_set1 => /(_ P0)Pr.
    move: perfectP.
    rewrite Pr.
    exact: perfect_set1.
  move/lebesgue_measure_gt0 => /(_ compactP itv_P P0).
  by rewrite muP ltxx.
have := bigcup_contiguous_intervals_fine compactP.
rewrite -/U => {}UE.
have {}UE : U = \big[setU/set0]_(k <- p)
    `](contiguous_intervals1 P k), (contiguous_intervals2 P k)[%classic.
  rewrite -bigcup_seq bigcup_mkcond UE; apply: eq_bigcupr => i _.
  case: ifPn => //.
  rewrite -Pp notin_setE.
  rewrite /contiguous_intervals_support/= => /nonemptyPn.
  rewrite /contiguous_intervals1 /contiguous_intervals2/= => ->/=.
  by rewrite inf0 sup0 set_itv_ge// bnd_simp ltxx.
pose unsorted_bnds := [seq ((contiguous_intervals1 P i),
                            (contiguous_intervals2 P i)) | i <- p].
pose le1 := fun x y : R * R => x.1 <= y.1.
have total_le1 : total le1.
  move=> [x1 x2] [y1 y2].
  by rewrite /le1/= le_total.
pose sorted_bnds := sort le1 unsorted_bnds.
have [h hsorted_bnds] := perm_iota_sort le1 0 unsorted_bnds.
rewrite -/sorted_bnds; move=> /= sorted_bndsE.
have {}UE : U = \big[setU/set0]_(k < size p)
    `](nth 0 sorted_bnds k).1, (nth 0 sorted_bnds k).2[%classic.
  rewrite UE.
  have pE : p = map (fun i => nth 0 p i) (iota 0 (size p)).
    by rewrite map_nth_iota ?subn0// drop0 take_size.
  rewrite [in LHS](perm_big [seq p`_i | i <- h])//=; last first.
    rewrite {1}pE.
    apply: perm_map.
    by rewrite perm_sym (perm_trans hsorted_bnds)// size_map.
  rewrite big_map.
  apply/esym.
  rewrite -(big_mkord xpredT (fun k => `](sorted_bnds`_k).1, (sorted_bnds`_k).2[%classic)).
  rewrite (_ : size p = size sorted_bnds); last first.
    by rewrite pE size_map size_iota size_sort size_map.
  rewrite -(@big_nth _ set0 setU _ 0 sorted_bnds xpredT (fun i => `]i.1, i.2[%classic)).
  rewrite sorted_bndsE big_map//.
  rewrite big_seq [in RHS]big_seq; apply: eq_bigr => /= i ih.
  have ip : (i < size p)%N.
    have := perm_mem hsorted_bnds => /(_ i).
    by rewrite ih mem_iota leq0n add0n/= size_map => <-.
  by rewrite (nth_map 0).
pose n := size p.
have PU : P = [set` Rhull P] `\` U.
  by rewrite /U /cplt_hull setDD setIidr//; exact: sub_Rhull.
have L3 : forall i, (i < (size p).-1)%N ->
  exists2 j, (j < size p)%N & unsorted_bnds`_j = sorted_bnds`_i.
  move=> i0 i0p.
  have K1 : sorted_bnds`_i0 \in unsorted_bnds.
    (* TODO: too long! *)
    rewrite sorted_bndsE.
    rewrite (nth_map 0); last first.
      by rewrite (perm_size hsorted_bnds) size_iota size_map (leq_trans i0p)// leq_pred.
    apply/(nthP 0).
    exists (h`_i0) => //.
    have : h`_i0 \in h.
      apply/(nthP 0); exists i0 => //.
      by rewrite (perm_size hsorted_bnds) size_iota size_map (leq_trans i0p)// leq_pred.
    by rewrite (perm_mem hsorted_bnds) mem_iota leq0n add0n/=.
  move: K1 => /(nthP 0)[j]; rewrite size_map => Hj HjE.
  by exists j.
have L4 : forall i, (i < (size p).-1)%N ->
  exists2 j, (j < size p)%N & unsorted_bnds`_j = sorted_bnds`_i.+1.
  move=> i0 i0p.
  have K2 : sorted_bnds`_i0.+1 \in unsorted_bnds.
    rewrite sorted_bndsE.
    rewrite (nth_map 0); last first.
      rewrite (perm_size hsorted_bnds) size_iota size_map.
      by rewrite -(@prednK (size p))// lt0n size_eq0.
    apply/(nthP 0); exists (h`_i0.+1) => //.
    rewrite size_map.
    have : h`_i0.+1 \in h.
      apply/(nthP 0); exists i0.+1 => //.
      rewrite (perm_size hsorted_bnds) size_iota size_map.
      by rewrite -(@prednK (size p))// lt0n size_eq0.
    rewrite (perm_mem hsorted_bnds) mem_iota leq0n add0n/=.
    by rewrite size_map.
  move: K2 => /(nthP 0)[k]; rewrite size_map => Hk HkE.
  by exists k.
have L5 : forall i, (i < size p)%N ->
    exists2 j, (j \in p)%N &
      (sorted_bnds`_i) = (contiguous_intervals1 P j, contiguous_intervals2 P j).
    move=> i pi.
    have hih : nth 0 h i \in h.
      apply/(nthP 0); exists i => //.
      by rewrite (perm_size hsorted_bnds) size_iota size_map.
    exists (nth 0 p (nth 0 h i)) => //.
      apply/(nthP 0).
      exists (h`_i) => //.
      move: hih.
      by rewrite (perm_mem hsorted_bnds) mem_iota add0n leq0n/= size_map.
    rewrite sorted_bndsE (nth_map 0)//; last first.
      by rewrite (perm_size hsorted_bnds)// size_iota size_map.
    rewrite (nth_map 0)//.
    move: hih.
    by rewrite (perm_mem hsorted_bnds) mem_iota add0n leq0n/= size_map.
have {}UE : [set` Rhull P] `\` U = `[inf P, (nth 0 sorted_bnds 0).1]%classic
    `|` (\big[setU/set0]_(k < n.-1)
        `[(nth 0 sorted_bnds k).2, (nth 0 sorted_bnds k.+1).1]%classic)
    `|` `[(nth 0 sorted_bnds n.-1).2, sup P]%classic.
  rewrite [in LHS]UE.
  rewrite -[in LHS](@prednK (size p)); last by rewrite lt0n size_eq0.
  rewrite compact_Rhull//.
  have itv_neq0 x : x \in unsorted_bnds -> `]x.1, x.2[ !=set0.
    rewrite /= => /mapP[/= i ip ->/=].
    have : contiguous_intervals_support P i by rewrite Pp/=.
    rewrite /contiguous_intervals_support/=.
    rewrite -contiguous_ooitv//.
      exact: (subset_has_ubound Pab).
    exact: (subset_has_lbound Pab).
  have sort1 : [seq (sorted_bnds`_i).1 | i <- iota 0 (size p)] =
               sort <=%R [seq contiguous_intervals1 P i | i <- p].
    rewrite (map_comp fst).
    rewrite map_nth_iota; last first.
      by rewrite subn0 size_sort size_map.
    rewrite drop0.
    rewrite (_ : size p = size sorted_bnds)//; last first.
      by rewrite size_sort size_map.
    rewrite take_size.
    rewrite /sorted_bnds.
    rewrite -sort_map.
    congr sort.
    rewrite /unsorted_bnds.
    rewrite -(map_comp fst)/=.
    by apply: eq_map => x/=.
  have H1 : sorted <=%R [seq (sorted_bnds`_i).1 | i <- iota 0 (size p)].
    rewrite sort_sorted_fst_iota//; last first.
      by rewrite /sorted_bnds size_sort size_map.
    by apply: sort_sorted; exact: total_le1.
  rewrite (@setD_bigcup_itvoo _ _ _ (fun k => (sorted_bnds`_k).1)
                              (fun k => (sorted_bnds`_k).2))//; last 4 first.
  - move=> i.
    rewrite prednK; last by rewrite lt0n size_eq0.
    move=> ip.
    have [j [jp ij]] := L5 _ ip.
    rewrite ij -compact_Rhull//.
    apply/sub_Rhull.
    apply: mem_contiguous_intervals2 => //.
    rewrite contiguous_ooitv//; last 2 first.
      exact: (subset_has_ubound Pab).
      exact: (subset_has_lbound Pab).
    have : (contiguous_intervals1 P j, contiguous_intervals2 P j) \in unsorted_bnds.
      rewrite -ij sorted_bndsE (nth_map 0); last first.
        by rewrite (perm_size hsorted_bnds)// size_iota size_map.
      apply/(nthP 0); exists (nth 0 h i) => //.
      rewrite size_map.
      have : nth 0 h i \in h.
        apply/(nthP 0); exists i => //.
        by rewrite (perm_size hsorted_bnds) size_iota size_map.
      by rewrite (perm_mem hsorted_bnds) mem_iota add0n leq0n/= size_map.
    by move/itv_neq0 => /=.
  - by rewrite prednK; last by rewrite lt0n size_eq0.
  - rewrite prednK; last by rewrite lt0n size_eq0.
    pose q := [seq nth 0 p i | i <- h].
    have pq : size q = size p.
      by rewrite /q size_map (perm_size hsorted_bnds) size_iota size_map.
    have [qE1 qE2] :
        [seq (sorted_bnds`_i).1 | i <- iota 0 (size p)] =
        [seq contiguous_intervals1 P i | i <- q] /\
        [seq (sorted_bnds`_i).2 | i <- iota 0 (size p)] =
        [seq contiguous_intervals2 P i | i <- q].
      split.
        rewrite [in LHS]sorted_bndsE.
        rewrite (map_comp fst).
        rewrite map_nth_iota; last first.
          by rewrite size_map subn0 (perm_size hsorted_bnds) size_iota size_map.
        rewrite drop0.
        rewrite (_ : size p = size ([seq unsorted_bnds`_i | i <- h])); last first.
          by rewrite size_map (perm_size hsorted_bnds) size_iota size_map.
        rewrite take_size.
        rewrite -(map_comp fst)/=.
        rewrite -map_comp/=.
        apply/eq_in_map => // x/= zh.
        rewrite /unsorted_bnds/=.
        rewrite (nth_map 0)//=.
        rewrite -pq size_map.
        move: zh.
        rewrite (perm_mem hsorted_bnds) mem_iota leq0n add0n/= size_map.
        by rewrite (perm_size hsorted_bnds) size_iota size_map.
      rewrite [in LHS]sorted_bndsE.
      rewrite (map_comp snd).
      rewrite map_nth_iota; last first.
        by rewrite size_map subn0 (perm_size hsorted_bnds) size_iota size_map.
      rewrite drop0.
      rewrite (_ : size p = size ([seq unsorted_bnds`_i | i <- h])); last first.
        by rewrite size_map (perm_size hsorted_bnds) size_iota size_map.
      rewrite take_size.
      rewrite -(map_comp snd)/=.
      rewrite -map_comp/=.
      apply/eq_in_map => // x/= zh.
      rewrite /unsorted_bnds/=.
      rewrite (nth_map 0)//=.
      rewrite -pq size_map.
      move: zh.
      rewrite (perm_mem hsorted_bnds) mem_iota leq0n add0n/= size_map.
      by rewrite (perm_size hsorted_bnds) size_iota size_map.
    rewrite qE2.
    apply: contiguous_intervals_sort => //.
    by move: compactP; rewrite Rcompact_boundE => -[].
    by move: compactP; rewrite Rcompact_boundE => -[].
    have ->// : [set` q] = [set` p].
    apply/seteqP; split.
      move=> /=r /mapP[/= i].
      rewrite (perm_mem hsorted_bnds) mem_iota leq0n/= add0n.
      rewrite size_map => pi ->.
      by apply/(nthP 0); exists i.
    move=> /= i /(nthP 0)[j jp <-].
    apply/mapP; exists j => //.
    rewrite (perm_mem hsorted_bnds) mem_iota leq0n/= add0n.
    by rewrite size_map.
    by rewrite Pp.
    by rewrite -qE1.
  - move=> i pi.
    have ? : (i < size p)%N by rewrite (leq_trans pi)// leq_pred.
    have ? : (i.+1 < size p)%N by rewrite -(@prednK (size p)) ?lt0n ?size_eq0.
    have H2 : (sorted_bnds`_i).1 <= (sorted_bnds`_i.+1).1.
      rewrite fst_map; last by rewrite size_sort size_map.
      rewrite fst_map; last by rewrite size_sort size_map.
      apply: le_sorted_leq_nth => //; last 2 first.
      - by rewrite inE size_map size_sort size_map (leq_trans pi)// leq_pred.
      - by rewrite inE/= size_map size_sort size_map.
      rewrite sorted_map.
      apply: sort_sorted => x y.
      exact: le_total.
    have H3 : (sorted_bnds`_i).2 <= (sorted_bnds`_i.+1).2.
      have [j Hj HjE] := L3 i pi.
      have [k Hk HkE] := L4 i pi.
      rewrite -HjE -HkE !(nth_map 0)//=.
      apply: contiguous_intervals_sort' => //.
      by move: compactP; rewrite Rcompact_boundE/= => -[].
      by move: compactP; rewrite Rcompact_boundE/= => -[].
      suff: contiguous_intervals_support P p`_k by [].
      rewrite Pp/=.
      by apply/(nthP 0); exists k.
      move: H2.
      move: HjE; rewrite (nth_map 0)//=.
      move: HkE; rewrite (nth_map 0)//=.
      by move=> <- <-.
    have [j Hj HjE] := L3 i pi.
    have [k Hk HkE] := L4 i pi.
    move: H2 H3.
    rewrite -HkE -HjE.
    rewrite !(nth_map 0)//= => H2 H3.
    have [jk|jk] := eqVneq (p`_j) (p`_k); last first.
      rewrite leNgt; apply/negP => i1i.
      pose m := ((contiguous_intervals1 P p`_k) + (contiguous_intervals2 P p`_j)) / 2.
      have : m \in contiguous_intervals P p`_j `&` contiguous_intervals P p`_k.
        rewrite contiguous_ooitv//; last 2 first.
        by move: compactP; rewrite Rcompact_boundE/= => -[].
        by move: compactP; rewrite Rcompact_boundE/= => -[].
        rewrite contiguous_ooitv//; last 2 first.
        by move: compactP; rewrite Rcompact_boundE/= => -[].
        by move: compactP; rewrite Rcompact_boundE/= => -[].
        rewrite !inE/= !in_itv/=; split.
          apply/andP; split.
            by rewrite /m (le_lt_trans H2)// midf_lt//.
          by rewrite /m midf_lt//.
        apply/andP; split.
          by rewrite /m midf_lt//.
        rewrite /m.
        rewrite (lt_le_trans _ H3)//.
        by rewrite midf_lt//.
      have /trivIsetP/(_ _ _ Logic.I Logic.I jk) := @disjoint_contiguous_intervals _ P.
      move=> ->.
      by rewrite in_set0.
    move: jk => /eqP.
    rewrite nth_uniq// => /eqP jk; subst k.
    move: HjE.
    rewrite HkE.
    rewrite sorted_bndsE.
    rewrite (nth_map 0)//; last first.
      by rewrite (perm_size hsorted_bnds) size_iota size_map.
    rewrite [in X in _ = X -> _](nth_map 0); last first.
      by rewrite (perm_size hsorted_bnds) size_iota size_map.
    rewrite /unsorted_bnds/= => /eqP.
    rewrite nth_uniq; last 3 first.
      rewrite size_map.
      have : h`_i.+1 \in h.
        apply/(nthP 0); exists i.+1 => //.
        by rewrite (perm_size hsorted_bnds) size_iota size_map.
      rewrite (perm_mem hsorted_bnds) mem_iota leq0n add0n/=.
      by rewrite size_map.
      rewrite size_map.
      have : h`_i \in h.
        apply/(nthP 0); exists i => //.
        by rewrite (perm_size hsorted_bnds) size_iota size_map.
      rewrite (perm_mem hsorted_bnds) mem_iota leq0n add0n/=.
      by rewrite size_map.
      apply/(uniqP 0) => x y/=.
      rewrite !inE !size_map => xp yp Hxy.
      apply/eqP/negPn/negP => xy.
      rewrite !(nth_map 0)// in Hxy.
      have {}xy : p`_x != p`_y by rewrite (nth_uniq 0).
      have /trivIsetP/(_ _ _ Logic.I Logic.I xy) := @disjoint_contiguous_intervals _ P.
      rewrite (contiguous_ooitv); last 2 first.
        exact: (subset_has_ubound Pab).
        exact: (subset_has_lbound Pab).
      rewrite (contiguous_ooitv); last 2 first.
        exact: (subset_has_ubound Pab).
        exact: (subset_has_lbound Pab).
      case: Hxy => -> ->.
      rewrite setIid => /eqP.
      apply/negP/set0P.
      rewrite -(contiguous_ooitv); last 2 first.
        exact: (subset_has_ubound Pab).
        exact: (subset_has_lbound Pab).
      move: Pp.
      rewrite /contiguous_intervals_support/= => /(congr1 (fun x => x p`_y))/= ->.
      by apply/(nthP 0); exists y.
    have := perm_uniq hsorted_bnds.
    rewrite iota_uniq => hu.
    rewrite nth_uniq//; last 2 first.
      by rewrite (perm_size hsorted_bnds) size_iota size_map.
      by rewrite (perm_size hsorted_bnds) size_iota size_map.
    rewrite -addn1.
    rewrite -{2}(addn0 i).
    by rewrite eqn_add2l.
  - move=> i.
    rewrite prednK// ?lt0n ?size_eq0// => pi.
    have [j jp ij] := L5 _ pi.
    rewrite ij/=.
    have : P (contiguous_intervals1 P j).
      apply: mem_contiguous_intervals1 => //.
      move: Pp.
      rewrite /contiguous_intervals_support/=.
      move/(congr1 (fun x => x j)).
      by rewrite /= jp => ->.
    suff : P `<=` `[inf P, sup P].
      by move=> /[apply] /=.
    apply: (subset_trans (@sub_Rhull _ _)) => //.
    by rewrite (compact_Rhull compactP P0)//.
admit.
Admitted.

Lemma contiguous_intervals_support0 (Z : set R) :
  ~ (closed Z) ->
  contiguous_intervals_support Z = set0.
Proof.
move=> ncZ.
rewrite /contiguous_intervals_support.
rewrite -set_false.
apply: eq_set => x; rewrite inE.
rewrite propeqE falseE; split => //.
move/set0P/negP; apply/negP/eqP.
rewrite /contiguous_intervals.
by case : (pselect (closed Z)).
Qed.

Lemma contiguous_intervals_nonempty (Z : set R) :
  Z != setT ->
   contiguous_intervals_support Z !=set0 -> Z !=set0.
Proof.
move=> nZT [n [x cgitvZx]].
have cZ : closed Z.
  apply: contrapT => /contiguous_intervals_support0.
  by apply/eqP/negP/negP/set0P; exists n; exists x.
apply/set0P/negP => /eqP Z0.
have : cplt_hull Z !=set0.
  rewrite bigcup_contiguous_intervals//.
  exists x; exists n => //.
apply/set0P/negP/negPn/eqP; rewrite Z0; exact: cplt_hull0.
Qed.

Lemma contiguous_intervals_set0 (i : nat) :
  @contiguous_intervals R set0 i = set0.
Proof.
apply/eqP/not_notP; move/negP/set0P => -[x i0].
have := @cplt_hull_set0 R.
move/eqP; apply/negP/set0P.
exists x.
rewrite bigcup_contiguous_intervals; last exact: closed0.
by exists i.
Qed.

Lemma contiguous_intervals_support_not_subset1 (Z : set R) n :
  contiguous_intervals_support Z n ->
  ~ is_subset1 (contiguous_intervals Z n).
Proof.
move/(is_subset1_set1) => H /H {}H.
apply: (@set1_not_open _ (xget point (contiguous_intervals Z n))).
rewrite -H.
exact: open_contiguous_intervals.
Qed.

Lemma contiguous_support_bnd_lt (Z : set R) (i : nat) :
  compact Z ->
  contiguous_intervals_support Z i ->
  contiguous_intervals1 Z i < contiguous_intervals2 Z i.
Proof.
move=> cZ.
rewrite /contiguous_intervals_support/= => cgiZ0.
have [Z0|Z0] := pselect (Z !=set0); last first.
  have {}Z0 : Z = set0 by apply/eqP/not_notP; move/negP/set0P.
  move: cgiZ0; rewrite Z0 contiguous_intervals_set0.
  by move/set0P/negP.
apply: has_bound_not_subset1_inf_sup.
- apply: (@subset_has_lbound _ _ _ ([set` Rhull Z])).
    apply: (subset_trans (@contiguous_intervalsS _ _ _)).
    exact: cplt_hull_subset_Rhull.
- rewrite (compact_Rhull cZ Z0).
  exact: has_lbound_itv.
- move: cZ; rewrite Rcompact_boundE => -[_ ubZ lbZ].
  rewrite (contiguous_ooitv ubZ lbZ).
  exact: has_ubound_itv.
exact: contiguous_intervals_support_not_subset1.
Qed.

End contiguous_intervals_support.

Module lemma6_direct_new.
Section lemma6_direct.
Context {R : realType}.
Local Notation mu := (@completed_lebesgue_measure R).

Variables a b : R.
Hypothesis ab : a < b.
Variable f : R -> R.
Hypotheses (cf : {within `[a, b], continuous f})
           (bvf : bounded_variation a b f)
           (lusinf : lusinN `[a, b] f).
Definition H := fun x => fine (total_variation a ^~ f x).

(* "Clearly, H is increasing and continuous. " *)
Let ndH := nondecreasing_total_variation bvf.
Let cH : {within `[a, b], continuous H}.
Proof. exact: total_variation_continuous. Qed.

(* https://math.stackexchange.com/questions/1925764/limit-point-of-the-set-of-limit-points-is-in-the-set-of-limit-points *)
Lemma limit_point_redundant (Z : set R) L :
  L = limit_point Z -> limit_point L `<=` L.
(* there is another proof using the fact that limit_point is closed *)
Proof.
move=> LE.
move=> /= p limlimZp.
rewrite LE.
apply/limit_point_open => U pU.
simpl in *.
have [y yp ULy] : exists2 y, y != p & (U `&` L) y.
  have [y [yp Ly Uy]] := limlimZp _ (open_nbhs_nbhs pU).
  by exists y => //.
have [V yV Vp] : exists2 V, nbhs y V & ~ V p.
  have : hausdorff_space R by [].
  rewrite ball_hausdorff => /(_ _ _ yp) -[[r1 r2]/=] => /eqP yr1pr2.
  exists (ball y r1%:num).
    exact: nbhsx_ballx.
  move=> yr1p.
  move: yr1pr2.
  rewrite -subset0.
  move/(_ p).
  by apply; split => //.
have UVy : (U `&` V) y.
  split.
    by case: ULy.
  by apply: nbhs_singleton.
have [z UVZz] : exists z, ((U `&` V) `&` Z) z.
  have : L y by case: ULy.
  rewrite LE.
  rewrite /limit_point/=.
  have : nbhs y (U `&` V).
    apply: filterI => //.
    apply: open_nbhs_nbhs.
    split => //.
      by case: pU.
    by case: UVy.
  move=> /[swap] /[apply] -[z [zy Zz UVz]].
  by exists z; split => //.
have zp : z != p.
  have zV : V z by case: UVZz => -[].
  by apply/eqP => ?; subst z.
exists z; split => //.
by case: UVZz.
by case: UVZz => -[].
Qed.

Definition contiguous_intervals12 (A : set R) :
  nat -> (R * R) :=
  fun n => (contiguous_intervals1 A n, contiguous_intervals2 A n).

Lemma contiguous_intervals_Rhull (A : set R) (cA : closed A) :
  \bigcup_k contiguous_intervals A k `|` A = [set` Rhull A].
Proof.
rewrite -bigcup_contiguous_intervals//.
by rewrite /cplt_hull setDKU//; exact: sub_Rhull.
Qed.

Lemma Ritv_open_bounded (b0 b1 : bool) (x y : R) :
  open [set` (Interval (BSide b0 x) (BSide b1 y))] =
   (~~ b0 && b1) || (y < x ?<= if ~~ b0 || b1).
Proof.
have e20 (e : R) (e0 : 0 < e) : 0 < e / 2 by rewrite divr_gt0.
have e2e (e : R) (e0 : 0 < e) : e / 2 < e.
  by rewrite {2}(splitr e) ltrDr (e20 _ e0).
have e40 (e : R) (e0 : 0 < e) : 0 < e / 2^+2 by rewrite divr_gt0.
have e42 (e : R) (e0 : 0 < e) : e / 2 ^+ 2 < e / 2.
  rewrite expr2 invfM mulrA.
  rewrite gtr_pMr//; last exact: e20.
  rewrite invf_lt1//.
  by rewrite (_ : 1 = 1%:R)// ltr_nat.
case: b0; case: b1 => //=; rewrite ?orbF ?orbT.
- rewrite propeqE; split; last first.
    move=> yx.
    by rewrite set_itv_ge// bnd_simp -leNgt.
  apply: contraPP.
  move/negP; rewrite -ltNge => xy.
  move/open_itvoo_subset.
  move/(_ x).
  rewrite /= in_itv/= xy lexx/= => /(_ isT).
  move=> [e /= e0].
  move/(_ (e / 2)) => /=.
  rewrite sub0r normrN gtr0_norm ?e20// e2e// => /(_ isT isT).
  move/(_ (x - e / (2^+2))) => /=.
  have sub_itv : x - e / 2 ^+ 2 \in `]x - e / 2, x + e / 2[.
    rewrite in_itv/=; apply/andP; split.
      by rewrite ler_ltB// e42//.
    rewrite ltrD2l.
    apply: (lt_trans _ (e42 _ e0)).
    by rewrite gtrN ?e40.
  move/(_ sub_itv).
  rewrite in_itv/=.
  apply/negP.
  rewrite negb_and; apply/orP; left.
  rewrite -ltNge.
  by rewrite gtrBl e40.
- rewrite propeqE; split; last first.
    by move=> yx; rewrite set_itv_ge// bnd_simp -ltNge.
  apply: contraPP; move/negP; rewrite -leNgt => xy.
  move/open_itvoo_subset.
  move/(_ x).
  rewrite /= in_itv/= xy lexx/= => /(_ isT).
  move=> [e /= e0].
  move/(_ (e / 2)) => /=.
  rewrite sub0r normrN gtr0_norm ?e20// e2e// => /(_ isT isT).
  move/(_ (x - e / (2^+2))) => /=.
  have sub_itv : x - e / 2 ^+ 2 \in `]x - e / 2, x + e / 2[.
    rewrite in_itv/=; apply/andP; split.
      by rewrite ler_ltB//  e42//.
    rewrite ltrD2l.
    apply: (lt_trans _ (e42 _ e0)).
    by rewrite gtrN ?e40.
  move/(_ sub_itv).
  rewrite in_itv/=.
  apply/negP.
  rewrite negb_and; apply/orP; left.
  rewrite -ltNge.
  by rewrite gtrBl e40.
- by rewrite propeqE; split.
- rewrite propeqE; split; last first.
    by move=> yx; rewrite set_itv_ge// bnd_simp -leNgt.
  apply: contraPP; move/negP; rewrite -ltNge => xy.
  move/open_itvoo_subset.
  move/(_ y).
  rewrite /= in_itv/= xy lexx/= => /(_ isT).
  move=> [e /= e0].
  move/(_ (e / 2)) => /=.
  rewrite sub0r normrN gtr0_norm ?e20// e2e// => /(_ isT isT).
  move/(_ (y + e / (2^+2))) => /=.
  have sub_itv : y + e / 2 ^+ 2 \in `]y - e / 2, y + e / 2[.
    rewrite in_itv/=; apply/andP; split.
      rewrite ler_ltD//.
      apply: (lt_trans _ (e40 _ e0)).
      by rewrite ltrNl oppr0 e20.
    by rewrite ltrD2l e42.
  move/(_ sub_itv).
  rewrite in_itv/=.
  apply/negP.
  rewrite negb_and; apply/orP; right.
  rewrite -ltNge.
  by rewrite ltrDl e40.
Qed.

Lemma Ritv_open_lray (b0 : bool) (x : R) :
  open [set` (Interval (BSide b0 x) (BInfty _ false))] = ~~ b0.
Proof.
have e20 (e : R) (e0 : 0 < e) : 0 < e / 2 by rewrite divr_gt0.
have e2e (e : R) (e0 : 0 < e) : e / 2 < e.
  by rewrite {2}(splitr e) ltrDr (e20 _ e0).
have e40 (e : R) (e0 : 0 < e) : 0 < e / 2^+2 by rewrite divr_gt0.
have e42 (e : R) (e0 : 0 < e) : e / 2 ^+ 2 < e / 2.
  rewrite expr2 invfM mulrA.
  rewrite gtr_pMr//; last exact: e20.
  rewrite invf_lt1//.
  by rewrite (_ : 1 = 1%:R)// ltr_nat.
case: b0 => /=.
- rewrite propeqE; split => //.
  rewrite falseE.
  move/open_itvoo_subset.
  move/(_ x).
  rewrite /= in_itv/= lexx/= => /(_ isT).
  move=> [e /= e0].
  move/(_ (e / 2)) => /=.
  rewrite sub0r normrN gtr0_norm ?e20// e2e// => /(_ isT isT).
  move/(_ (x - e / (2^+2))) => /=.
  have sub_itv : x - e / 2 ^+ 2 \in `]x - e / 2, x + e / 2[.
    rewrite in_itv/=; apply/andP; split.
      by rewrite ler_ltB// e42//.
    rewrite ltrD2l.
    apply: (lt_trans _ (e42 _ e0)).
    by rewrite gtrN ?e40.
  move/(_ sub_itv).
  rewrite in_itv/=.
  apply/negP.
  rewrite negb_and; apply/orP; left.
  rewrite -ltNge.
  by rewrite gtrBl e40.
by rewrite propeqE; split.
Qed.

Lemma Ritv_open_rray (b1 : bool) (y : R) :
  open [set` (Interval (BInfty _ true) (BSide b1 y))] = b1.
Proof.
have e20 (e : R) (e0 : 0 < e) : 0 < e / 2 by rewrite divr_gt0.
have e2e (e : R) (e0 : 0 < e) : e / 2 < e.
  by rewrite {2}(splitr e) ltrDr (e20 _ e0).
have e40 (e : R) (e0 : 0 < e) : 0 < e / 2^+2 by rewrite divr_gt0.
have e42 (e : R) (e0 : 0 < e) : e / 2 ^+ 2 < e / 2.
  rewrite expr2 invfM mulrA.
  rewrite gtr_pMr//; last exact: e20.
  rewrite invf_lt1//.
  by rewrite (_ : 1 = 1%:R)// ltr_nat.
  case: b1 => //=.
- by rewrite propeqE; split.
rewrite propeqE; split => //.
rewrite falseE.
move/open_itvoo_subset.
move/(_ y).
rewrite /= in_itv/= lexx/= => /(_ isT).
move=> [e /= e0].
move/(_ (e / 2)) => /=.
rewrite sub0r normrN gtr0_norm ?e20// e2e// => /(_ isT isT).
move/(_ (y + e / (2^+2))) => /=.
have sub_itv : y + e / 2 ^+ 2 \in `]y - e / 2, y + e / 2[.
  rewrite in_itv/=; apply/andP; split.
    rewrite ler_ltD//.
    apply: (lt_trans _ (e40 _ e0)).
    by rewrite ltrNl oppr0 e20.
  by rewrite ltrD2l e42.
move/(_ sub_itv).
rewrite in_itv/=.
apply/negP.
rewrite -ltNge.
by rewrite ltrDl e40.
Qed.

Lemma not_bounded_set_lray (b0 : bool) (r : R) :
   ~ bounded_set [set` (Interval (BSide b0 r) (BInfty _ false))].
Proof.
suff hubr : ~ has_ubound [set z | r < z].
case: b0; rewrite set_itvE Rbounded_setE; apply/not_andP; right => //.
  apply/forallNP => x.
  have/forallNP/(_ x) := hubr.
  move/existsNP => [z/= /not_implyP[rz /negP]]; rewrite -ltNge => xz.
  apply/existsNP; exists z.
  by apply/not_implyP; split; [|apply/negP]; rewrite /= -?ltNge ?ltW.
apply/forallNP => x.
move/(_ (`|r| + 1 + (`|x| + 1))) => /=.
have rrx : r < `|r| + 1 + (`|x| + 1).
  rewrite -{1}(addr0 r).
  apply: ltrD => //.
  by rewrite (@le_lt_trans _ _ `|r|) ?ltrDl ?ler_norm.
move/(_ rrx).
apply/negP.
rewrite -ltNge -{1}(add0r x).
rewrite ltrD => //.
by rewrite (@le_lt_trans _ _ `|x|) ?ltrDl ?ler_norm.
Qed.

Lemma not_bounded_set_rray (b0 : bool) (r : R) :
   ~ bounded_set [set` (Interval (BInfty _ true) (BSide b0 r))].
Proof.
suff hubr : ~ has_lbound [set z | z < r].
case: b0; rewrite set_itvE Rbounded_setE; apply/not_andP; left => //.
  apply/forallNP => x.
  have/forallNP/(_ x) := hubr.
  move/existsNP => [z/= /not_implyP[rz /negP]]; rewrite -ltNge => xz.
  apply/existsNP; exists z.
  by apply/not_implyP; split; [|apply/negP]; rewrite /= -?ltNge ?ltW.
apply/forallNP => x.
move/(_ (- (`|r| + 1 + (`|x| + 1)))) => /=.
have rxr : - (`|r| + 1 + (`|x| + 1)) < r.
  rewrite -{2}(addr0 r) opprD.
  apply: ltrD => //.
  rewrite (@lt_le_trans _ _ (- `|r|))//.
    by rewrite ltrN2 ltrDl.
  by rewrite lerNl -normrN ler_norm.
move/(_ rxr).
apply/negP.
rewrite -ltNge -{2}(add0r x).
rewrite opprD ltrD => //.
rewrite (@lt_le_trans _ _ (- `|x|))//.
  by rewrite ltrN2 ltrDl.
by rewrite lerNl -normrN ler_norm.
Qed.

Lemma not_bounded_setT : ~ (bounded_set (@setT R)).
Proof.
apply/forallNP => x.
rewrite -implypN => _.
move/(_ (`|x| + 1)).
have xx1 : x < `|x| + 1.
  apply: (le_lt_trans (ler_norm _)).
  by rewrite ltrDl.
move/(_ xx1).
apply/existsNP => /=.
exists (`|x| + 1 + 1).
apply/not_implyP; split => //.
apply/negP; rewrite -ltNge.
rewrite [ltRHS]ger0_norm//.
by rewrite ltrDl.
Qed.

Lemma nonempty_bounded_Rooitv (i : interval R) :
  [set` i] !=set0 -> open [set` i] -> bounded_set [set` i] ->
  exists a b : R, a < b /\ i = `]a, b[.
Proof.
case: i.
move=> [[l|l]|[]][[r|r]|[]];
  rewrite ?Ritv_open_bounded ?Ritv_open_lray ?Ritv_open_rray//=; last 10 first.
- move/[swap] => rl.
  by move/set0P; rewrite set_itv_ge ?eqxx// bnd_simp -leNgt.
- by rewrite set_itvE; move/set0P; rewrite eqxx.
- by move=> _ _ /not_bounded_set_lray.
- by move=> _ _ /not_bounded_set_rray.
- by rewrite set_itvE => /set0P/negP.
- by rewrite set_itvE => _ _ /not_bounded_setT.
- by rewrite set_itvE => /set0P/negP.
- by rewrite set_itvE => /set0P/negP.
- by rewrite set_itvE => /set0P/negP.
- by rewrite set_itvE => /set0P/negP.
- move/[swap] => rl; rewrite set_itv_ge; last by rewrite bnd_simp -leNgt.
  by move/set0P/negP.
- move/[swap] => rl; rewrite set_itv_ge; last by rewrite bnd_simp -ltNge.
  by move/set0P/negP.
- by rewrite set_itvE => /set0P/negP.
move=> [x/=]; rewrite in_itv/= => /andP[lx] /(lt_trans lx) {x lx} lr.
by exists l, r; split.
Qed.

Lemma nonempty_open_Rinterval_is_not_subset1 (i : interval R) :
  open [set` i] -> [set` i] !=set0 ->
  ~ (is_subset1 [set` i]).
Proof.
move=> oi [x ix].
have [e/= e0 He] := open_itvcc_subset oi ix.
have e2e : `|0 - e / 2| < e.
  rewrite sub0r normrN ger0_norm; last by rewrite mulr_ge0// ltW.
  rewrite {2}(splitr e) ltrDl.
  by rewrite mulr_gt0.
move/(_ (x - e / 2) (x + e / 2)).
apply/not_implyP; split.
  apply: (He (e / 2)) => //=.
    by rewrite mulr_gt0.
  by rewrite boundl_in_itv/= bnd_simp lerD2l ge0_cp// mulr_ge0// ltW.
apply/not_implyP; split.
  apply: (He (e / 2)) => //=.
    by rewrite mulr_gt0.
  by rewrite boundr_in_itv/= bnd_simp lerD2l ge0_cp// mulr_ge0// ltW.
apply/eqP; rewrite eq_le negb_and; apply/orP; right; rewrite -ltNge.
by rewrite ltrD2l gt0_cp// mulr_gt0.
(*
move=> oi.
have [bi|] := pselect (bounded_set [set` i]).
  move/nonempty_bounded_Rooitv /(_ oi bi) => [il [ir [ilr ->]]].
  move/(_ ((il *+ 2 + ir) / 3) ((il + ir *+ 2) / 3)).
  apply/not_implyP; split; [|apply/not_implyP; split].
  - admit.
  - admit.
  admit.
*)
Qed.

Lemma compact_mem_sup (A : set R) : compact A -> A (sup A).
Proof.
rewrite Rcompact_boundE => -[cA ubA _].
Abort.

Lemma compact_mem_inf (A : set R) : compact A -> A (inf A).
Proof.
Abort.

(*
Lemma lebesgue_measure_eq_itv_bnd (A : set R) (x y : R)
 (b0 b1 : bool) :
  (x <= y) ->
  A = [set` Interval (BSide b0 x) (BSide b1 y)] ->
  (lebesgue_measure A = (y - x)%:E)%E.
Proof.
rewrite le_eqVlt => /predU1P[->|].
  move=> ->; rewrite subrr.
  case: b0; case: b1; rewrite ?set_itvoo0 ?set_itvoc0 ?set_itvco0 ?measure0//.
  by rewrite set_itv1 lebesgue_measure_set1.
move=> xy ->.
by case: b0; case: b1; rewrite lebesgue_measure_itv lte_fin xy.
Qed.
*)

From mathcomp Require Import esum.

Section max_nngr.

Definition max_nngr := (@Order.max ring_display {nonneg R}).

(* HB.instance Definition _ := Monoid.Law.on max_nngr. *)

Lemma opA : @associative {nonneg R} max_nngr.
Admitted.

Lemma op1m : left_id (0%:nng : {nonneg R}) max_nngr.
Admitted.

Lemma opm1 : right_id (0%:nng : {nonneg R}) max_nngr.
Admitted.

HB.instance Definition _ := Monoid.isLaw.Build {nonneg R} 0%:nng
  max_nngr
   opA op1m opm1.

Lemma big_max_nngr_eq (r : seq nat) :
\big[max_nngr/0%:nng]_(i <- r) 0%:nng = 0%:nng.
Proof.
apply: big1_eq.
Abort.

End max_nngr.

Lemma completed_lebesgue_measure_eq_itv (A : set R) (x y : itv_bound R) :
  (x < y)%E ->
  A = [set` Interval x y] ->
  (mu A = ereal_of_itv_bound y - ereal_of_itv_bound x)%E.
Proof.
by move=> xy ->; rewrite completed_lebesgue_measure_itv xy.
Qed.

Lemma zip_nthE {A B : Type} (dx : A) (dy : B)
    (xs : seq A) (ys : seq B) :
  size xs = size ys ->
  [seq (nth dx xs i, nth dy ys i) | i <- iota 0 (size xs)] = zip xs ys.
Proof.
move=> xy.
apply: (@eq_from_nth _ (dx, dy)).
  by rewrite size_map size_iota size_zip xy minnn.
move=> j; rewrite size_map size_iota => Hj.
rewrite (nth_map 0%N); last by rewrite size_iota.
by rewrite nth_iota // add0n nth_zip.
Qed.

Lemma map_unzip_nth {A B C : Type} (da : A) (db : B)
    (F : A -> B -> C) (s : seq (A * B)) :
  [seq F (nth da (unzip1 s) i) (nth db (unzip2 s) i)
     | i <- iota 0 (size s)]
  = [seq F p.1 p.2 | p <- s].
Proof.
rewrite -[in RHS](zip_unzip s) -(zip_nthE da db); last by rewrite !size_map.
by rewrite -map_comp size_map.
Qed.

(* https://math.stackexchange.com/questions/520209/removing-isolated-points-to-get-a-perfect-set *)
Lemma lemma6_direct : lusinN `[a, b] H.
Proof.
apply: contrapT => nl.
(* use lemma 3 *)
have [Z [Zab cZ isoZ0 Z0 HZ]] : exists Z : set R,
    [/\ Z `<=` `[a, b], compact Z, isolated Z = set0,
        mu Z = 0 & (0%R < mu [set H x | x in Z])%E].
  (* lemma3 *)
  have := image_measure0_Lusin_nondecreasing_new ab cH ndH.
  move/contra_not => /(_ nl).
  move/existsNP=> [Z /not_implyP [Zab /not_implyP[cZ /not_implyP[isoZ0
/not_implyP[muZ0]]]]].
  move/eqP; rewrite neq_lt ltNge measure_ge0/= => muHZ_gt0.
  by exists Z.
move: (cZ); rewrite Rcompact_boundE => -[clZ ubZ lbZ].
have cHZ : compact (H @` Z).
  apply: (@continuous_compact _ _ H Z); last exact: cZ.
  exact: (continuous_subspaceW Zab).
pose c : R := inf Z.
pose d : R := sup Z.
have cd : c < d.
  apply: has_bound_not_subset1_inf_sup.
  - by exists a => ? /Zab/=; rewrite in_itv/= => /andP[].
  - by exists b => ? /Zab/=; rewrite in_itv/= => /andP[].
  move=> Z1.
  move: HZ.
  rewrite measure_gt0/= => /negP; apply; apply/eqP.
  apply: countable_lebesgue_measure0.
  apply: (@sub_countable _ _ _ Z).
    exact: card_image_le.
  exact: is_subset1_countable.
have perfectZ : perfect_set Z.
  by apply/perfectP; split.
have Z_nonempty : Z !=set0.
  apply/set0P; apply/negP => /eqP Z0'.
  by move: HZ; rewrite Z0' image_set0 measure0 ltxx.
have closedZ : closed Z by exact: compact_closed cZ.
pose supp := contiguous_intervals_support Z.
have infsupp := contiguous_infinite Zab cZ Z_nonempty Z0 perfectZ.
have countsupp : countable supp by exact: subset_card_le.
have /ppcard_eqP[/= h] := eq_card_nat countsupp infsupp.
pose h1 : {bij [set: nat] >-> supp} := h^-1%FUN.
have hh1 : {in supp, cancel h h1} by exact: funK.
have h1h : cancel h1 h by move=> x; apply: invK; rewrite inE.
have ne_cgitvs n : contiguous_intervals Z (h1 n) !=set0.
  have : supp (h1 n).
    have := @bij _ _ _ _ h1.
    by move=> [+ _ _]; exact.
  by rewrite /supp/contiguous_intervals_support/=.
pose A_ n := (contiguous_intervals1 Z (h1 n)).
pose B_ n := (contiguous_intervals2 Z (h1 n)).
have AB n : A_ n < B_ n.
  have : contiguous_intervals_support Z (h1 n).
  have := @bij _ _ _ _ h1.
  move=> [].
  by move/(_ n I).
  move=> [x].
  rewrite contiguous_ooitv//= in_itv/= => /andP[Ax xB].
  exact: lt_trans Ax xB.
pose alpha := mu (H @` Z).
have fin_alpha : alpha \is a fin_num.
  rewrite gt0_fin_numE//.
  apply: (@le_lt_trans _ _ (mu (H @` `[a, b]))).
    apply: le_outer_measure.
    exact: image_subset.
  apply: (@le_lt_trans _ _ (mu `[H a, H b])).
    apply: le_outer_measure.
    apply: continuous_nondecreasing_image_itvcc => //.
    exact: ltW.
  have [|] := ltP (H b) (H a).
    rewrite ltNge.
    by rewrite ndH ?boundl_in_itv ?boundr_in_itv ?bnd_simp//= ltW.
  rewrite le_eqVlt => /predU1P[->|HaHb].
    by rewrite set_itv1 completed_lebesgue_measureE lebesgue_measure_set1.
  rewrite completed_lebesgue_measure_itv ifT ?lte_fin//=.
  by rewrite -EFinB ltry.
pose AB_ n := [seq ((A_ i, B_ i), i) | i <- iota 0 n.+1].
pose ab_ n := sort (fun x y => x.1.1 <= y.1.1) (AB_ n).
(*
have nth_abE n i :
  (i < n.+1)%N ->
  let p := nth (d, d, 0%N) (ab_ n) i in
  [/\ p.1.1 = A_ p.2, p.1.2 = B_ p.2 & (p.2 < n.+1)%N].
  move=> iltn.
  split.
  - rewrite -(nth_map _ (d, d)).

  -
  -
*)
pose seq_a n := unzip1 (unzip1 (ab_ n)).
pose seq_b n := unzip2 (unzip1 (ab_ n)).
pose idxs n := unzip2 (ab_ n).
have sorted_a n : sorted <=%R (seq_a n).
  rewrite sorted_map ?sort_sorted// sorted_map sort_sorted//=.
  by move=> ? ?/=; rewrite le_total.
have sorted_b n : sorted <=%R (seq_b n).
  rewrite /seq_b.
  have [q H1 H2] := perm_iota_sort
    (fun x y : R * R * nat => x.1.1 <= y.1.1) (d, d, 0) (AB_ n).
  have qin i : i \in q -> (i < n.+1)%N.
    rewrite (perm_mem H1) mem_iota leq0n/= add0n.
    by rewrite size_map size_iota.
  rewrite -/(ab_ _) in H2.
  rewrite H2.
  rewrite [X in sorted _ X](_ : _ =
      ([seq nth d [seq B_ i | i <- iota 0 n.+1] i | i <- q])); last first.
    rewrite /unzip2.
    rewrite -2!map_comp.
    apply/eq_in_map => i iq.
    rewrite -compA [in LHS]/=.
    rewrite fst_map; last by (rewrite !size_map size_iota; exact: qin).
    rewrite snd_map; last by (rewrite !size_map size_iota; exact: qin).
    rewrite (nth_map (d, d)); last by (rewrite !size_map size_iota; exact: qin).
    rewrite nth_map_iota; last exact: qin.
    rewrite (nth_map (d, d, 0)); last first.
      by rewrite size_map size_iota; exact: qin.
    rewrite nth_map_iota//.
    exact: qin.
  rewrite [X in sorted _ X](_ : _ = [seq B_ i | i <- q]); last first.
    apply/eq_in_map => i iq.
    rewrite /B_.
    rewrite nth_map_iota//.
    exact: qin.
  rewrite /B_.
  rewrite map_comp.
  apply: contiguous_intervals_sort => //.
    move=> i/=.
    move/mapP => /= [j jq ->].
    have [+ _ _] := @bij _ _ _ _ h1; exact.
  rewrite -map_comp/=.
  rewrite [X in sorted _ X](_ : _ = [seq A_ i | i <- q])//.
  suff: sorted (fun x y : R * R * nat => x.1.1 <= y.1.1) (ab_ n).
    rewrite H2.
    evar (l : seq (R * R * nat)).
    rewrite (_ : [seq nth (d, d, 0) (AB_ n) i | i <- q] = l); last first.
      by apply: eq_map.
    rewrite {}/l.
    have -> : [seq A_ i | i <- q] =
               [seq nth d (unzip1 (unzip1 (AB_ n))) i | i <- q].
      apply/eq_in_map => i iq.
      have ? : (i < n.+1)%N.
        move: iq.
        by rewrite (perm_mem H1) mem_iota leq0n/= add0n size_map size_iota.
      by rewrite /AB_ /unzip1 -2!map_comp nth_map_iota.
    rewrite -sorted_map.
    rewrite -map_comp.
    under eq_map => i/=.
    have -> : (nth (d, d, 0) (AB_ n) i).1.1 = nth d (unzip1 (unzip1 (AB_ n))) i.
      have [iltSn|ni] := ltnP i n.+1.
        rewrite (nth_map (d, d)); last by rewrite !size_map size_iota.
        by rewrite (nth_map (d, d, 0))// !size_map size_iota.
      by rewrite !nth_default// !size_map size_iota.
    over.
    done.
  rewrite /ab_.
  apply: sort_sorted.
  by move=> ? ?/=; rewrite le_total.
pose a_ n := nth d (seq_a n).
pose b_ n := nth d (seq_b n).
pose idx n := nth 0 (idxs n) : nat -> nat.
have aleb n i : a_ n i <= b_ n i.
  admit.
have aE n i : (i < n.+1)%N -> a_ n i = A_ (idx n i).
  move=> iltn.
  rewrite /a_ /idx /idxs /seq_a /ab_ /AB_.
  rewrite !sort_map.
  rewrite -!zip_map !unzip1_zip ?unzip2_zip; last 3 first.
  - by rewrite size_zip !size_map !size_sort size_iota minnn.
  - by rewrite !size_map !size_sort size_iota.
  - by rewrite size_zip !size_map !size_sort size_iota minnn.
  rewrite -!sort_map.
  have : perm_eq [seq A_ i | i <- iota 0 n.+1] (seq_a n).
    admit.
  move/(perm_iotaP d) => [q].
  rewrite !size_map size_sort size_map size_iota.
  move/tuple_permP => [p qE] Aq.
  rewrite Aq.
  have [qa pqa sqE] := perm_iota_sort
  <=%R d [seq nth d (seq_a n) i | i <- q].
  rewrite sqE.
(*  
  rewrite -2![in RHS]zip_map.
  rewrite !unzip2_zip.
  rewrite (nth_map (d, d)); last first.
    admit.
  rewrite (nth_map (d, d, 0)); last first.
    admit.
  rewrite -[in LHS]zip_map.
  rewrite nth_zip.
  rewrite zip_unzip.
  rewrite unzip1_zip.
*)
  admit.
have clea n i : c <= a_ n i%N.
  admit.
have biled n i : b_ n i <= d.
  admit.
(*
Z : set R
contiguous_intervals Z :
[c   = c_0, d_0 = a_0]  ]a_0, b_0[
[c_1 = b_0, d_1 = a_1]  ]a_1, b_1[
[c_2 = b_1, d_2 = a_2]  ]a_2, b_2[
...
[c_n.-1 = b_m.-2, d_n.-1 = a_n.-1] ]a_n.-1, b_n.-1[
[c_n    = b_n.-1, d_n = a_n]       ]a_n, b_n[
[c_n.+1 = b_n, d_n.+1 = d]
*)
have blea : forall n i, (i < n.+1)%N -> b_ n.+1 i <= a_ n.+1 i.+1.
  (* disjoint_contiguous_intervals *)
  move=> n i ni.
  rewrite leNgt; apply/negP => aibi.
  have : `]a_ n.+1 i, b_ n.+1 i[ `&` `]a_ n.+1 i.+1, b_ n.+1 i.+1[ !=set0.
    rewrite [X in X !=set0](_ : _ = [set` `]a_ n.+1 i.+1, b_ n.+1 i[]); last first.
      rewrite -set_itvI/=.
      rewrite /Order.meet/=.
      apply/set_itvP => r/=.
      congr (_ \in _).
      rewrite join_r; last first.
        rewrite bnd_simp /a_.
        rewrite sorted_leq_nth ?inE//.
            exact: le_trans.
          by rewrite !size_map size_sort size_map size_iota (leq_trans ni).
        by rewrite !size_map size_sort size_map size_iota ltnS (leq_trans ni).
      rewrite meet_l//.
      rewrite bnd_simp.
      rewrite sorted_leq_nth ?inE//.
          exact: le_trans.
        by rewrite !size_map size_sort size_map size_iota (leq_trans ni)//.
      by rewrite !size_map size_sort size_map size_iota ltnS (leq_trans ni).
    exists ((a_ n.+1 i.+1 + b_ n.+1 i) / 2).
    rewrite /=.
    rewrite in_itv/= midf_lt//=.
    by rewrite midf_lt.
  rewrite /a_ /b_ /seq_a /seq_b.
  have : perm_eq [seq (contiguous_intervals Z (h1 i)) | i <- iota 0 n.+2]
         [seq `]a_ n.+1 i, b_ n.+1 i[%classic | i <- iota 0 n.+2].
    (* contiguous_ooitv *)
    under eq_map do rewrite contiguous_ooitv//.
    have {2}-> : n.+2 = size (unzip1 (ab_ n.+1)).
      by rewrite size_map size_sort size_map size_iota.
    rewrite (map_unzip_nth d d (fun l r => `]l, r[%classic)).
    (* *)
    have := (zip_map (fun i => (BRight (contiguous_intervals1 Z i)))
             (fun i => (BLeft (contiguous_intervals2 Z i))) (iota 0 n.+1)).
    admit.
  move/(@perm_eq_trivIset _ _ _ setT (subsetT _)).
  have triv_cgitv : trivIset [set: nat]
     [eta nth set0 [seq contiguous_intervals Z (h1 i1) | i1 <- iota 0 n.+2]].
    apply/trivIsetP.
    move=> j1 j2 _ _ => j12.
    rewrite map_comp.
    have [nj1|j1n] := ltnP n.+2 j1.+1.
      by rewrite nth_default ?size_map ?size_iota ?set0I.
    have [nj2|j2n] := ltnP n.+2 j2.+1.
      by rewrite [X in _ `&` X]nth_default ?size_map ?size_iota ?setI0.
    rewrite !(nth_map 0%N) ?size_map ?size_iota ?nth_iota// !add0n.
    have/trivIsetP := (@disjoint_contiguous_intervals _ Z).
    apply => //.
    apply/negP; move/eqP.
    have [_ injh1 _] := @bij _ _ _ _ h1; move/injh1.
    rewrite inE/= => /(_ I I).
    by move/eqP; apply/negP.
  move/(_ triv_cgitv).
  move/trivIsetP.
  move/(_ _ _ I I (negbT (ltn_eqF (ltnSn i)))).
  have nth_map_iota_itv k : (k < n.+2)%N ->
 nth set0 [seq `]a_ n.+1 i0, b_ n.+1 i0[%classic | i0 <- iota 0 n.+2] k =
     `]a_ n.+1 k, b_ n.+1 k[%classic.
    move=> kn.
    by rewrite nth_map_iota.
  rewrite !nth_map_iota_itv//; last exact: leq_trans ni.
  move=> H.
  move/set0P/negP.
  apply/negP.
  apply/eqP.
  done.
have lbZa : lbound Z a.
  move=> r Zr.
  have := Zab r Zr.
  by rewrite /= in_itv/= => /andP[].
have ubZb : ubound Z b.
  move=> r Zr.
  have := Zab r Zr.
  by rewrite /= in_itv/= => /andP[].
pose c_ n j := nth d (c :: [seq b_ n i | i <- iota 0 n]) j.
pose d_ n j := nth d (rcons [seq a_ n i | i <- iota 0 n] d) j.
have cled n i : c_ n.+1 i <= d_ n.+1 i.
  rewrite /c_ /d_.
  rewrite nth_rcons size_map size_iota.
  case: ifP => n0.
    rewrite nth_map_iota//.
    case: i n0.
      move=> _ /=.
      rewrite /a_.
      rewrite /ab_.
      rewrite /=.
      (* rewrite nth_zip. *)
      admit.
    move=> i.
    rewrite ltnS => iltn.
    rewrite (lock n.+1) /= -lock nth_map_iota; last by rewrite ltnS ltnW.
    by rewrite blea// (leq_trans iltn).
  rewrite if_same.
  move: n0.
  move/negP/negP; rewrite -ltnNge ltnS leq_eqVlt => /predU1P[<-|n1lti].
    rewrite [leLHS](_:_ = nth d [seq b_ n.+1 i0 | i0 <- iota 0 n.+1] n)//.
    rewrite nth_map_iota; last by [].
    exact: biled.
  by rewrite nth_default//= size_map size_iota.
pose lambda n := diam_max [seq `[c_ n i, d_ n i]%classic | i <- iota 0 n.+1].
have lambda_fin n : lambda n \is a fin_num.
  rewrite ge0_fin_numE; last exact: diam_max_ge0.
  case: n => [|n]; first by rewrite /lambda diam_max_seq1 diam_itv ?ltry// ltW.
  rewrite /lambda /diam_max big_seq_cond; apply: bigmax_lt; first by [].
  move=> s; rewrite andbT.
  move/mapP => [i].
  rewrite mem_iota add0n => /andP[_ iltn2 ->].
  by rewrite diam_itv ?ltry ?cled.
have lambda_ge0 n : (0 <= lambda n)%E.
  exact: diam_max_ge0.
have mcgitv i : mu.-cara.-measurable (contiguous_intervals Z i).
  move=> k; apply: sub_caratheodory.
  apply: open_measurable.
  exact: open_contiguous_intervals.
have lambda0 : (fine \o lambda) @ \oo --> 0%R.
  apply: fine_cvg.
  suff : lambda x.+1 @[x --> \oo] --> 0%:E.
    by rewrite cvg_shiftS.
  apply (@squeeze_cvge _ _ _ R (cst 0) _
    (fun n => \sum_(i < n.+2) mu `[c_ n.+1 i, d_ n.+1 i])).
      near=> n; apply/andP; split.
        exact: diam_max_ge0.
      rewrite /lambda /diam_max.
      rewrite big_tuple.
      apply: bigmax_le.
        exact: leNye.
      move=> /= i _.
      rewrite tnth_map.
      rewrite (tnth_nth 0).
      rewrite nth_iota// add0n.
      rewrite diam_itv; last exact: cled.
      rewrite (bigD1 i)//=.
      rewrite completed_lebesgue_measure_itv lte_fin.
        have [_|] := ltP (c_ n.+1 i) (d_ n.+1 i).
          rewrite /= -EFinB leeDl//.
          by rewrite sume_ge0.
        rewrite (le_eqVlt (d_ n.+1 i) (c_ n.+1 i)) => /predU1P[->|].
        rewrite subrr add0e.
        by apply: sume_ge0 => ? _.
      rewrite /c_ /d_.
      case: i; case => [? /=|].
        rewrite ltNge.
        have -> //: (c <= a_ n.+1 0%N).
        exact: clea.
      move=> i iltn.
      rewrite nth_rcons if_same.
      rewrite size_map size_iota.
      have -> : nth d (c :: [seq b_ n.+1 i0 | i0 <- iota 0 n.+1]) i.+1 =
         nth d [seq b_ n.+1 i0 | i0 <- iota 0 n.+1] i by [].
      case: ifP.
        move=> ilen.
        rewrite nth_map_iota//.
        rewrite nth_map_iota; last exact: ltn_trans ilen.
        by rewrite ltNge blea.
      move/negP/negP; rewrite -leqNgt => ni.
      have ieqn : i = n.
        by apply/eqP; rewrite eqn_leq; apply/andP; split.
      rewrite nth_map_iota; last by [].
      by rewrite ltNge biled.
    exact: cvg_cst.
  apply: (@cvg_trans _
  (mu (\bigcap_(i < n.+2) ([set` Rhull Z] `\` (contiguous_intervals Z i)))
             @[n --> \oo])).
    apply: near_eq_cvg.
    near=> n.
    admit.
  have <- : mu (\bigcap_n ([set` Rhull Z] `\` (contiguous_intervals Z n))) = 0%:E.
    rewrite bigcupDr//.
    rewrite -bigcup_contiguous_intervals//.
    rewrite setDD.
    rewrite setIidr; last exact: sub_Rhull.
    exact: Z0.
  rewrite (cvg_shiftS (fun n => mu (\bigcap_(i < n.+1)
              ([set` Rhull Z] `\` contiguous_intervals Z i)))).
  apply: bigcap_cvg_mu => /=; last 2 first.
      move=> ?.
      apply: measurableD => //.
      exact: sub_caratheodory.
    apply: bigcap_measurable => // ? _.
    apply: measurableD => //.
    exact: sub_caratheodory.
  apply: (@le_lt_trans _ _ (mu [set` Rhull Z])).
    apply: le_outer_measure.
    exact: subDsetl.
  rewrite compact_Rhull//.
  rewrite completed_lebesgue_measure_itv//= lte_fin.
  rewrite cd.
  by rewrite -EFinB ltry.
have nth_b_ n (i j : 'I_n) : (i <= j)%N -> b_ n i <= b_ n j.
  move=> ij.
  (*by apply: le_sorted_leq_nth => //; rewrite inE size_bE.*) admit.
have construct_x n :
  exists x : seq R, [/\ itv_partition c d (behead x),
    ((mesh c d (behead x))%:E <= lambda n)%E,
    (forall i : 'I_ n.+1, c_ n i \in x /\ d_ n i \in x),
    (n < size x)%N &
    (forall (i j : 'I_ n.+1), nth d x j \notin `]c_ n i, d_ n i[) ].
  admit.
pose x := fun n => sval (cid (@construct_x n)).
have pcdx n : itv_partition c d (behead (x n)).
  by have [] := proj2_sig (cid (@construct_x n)).
have max_x n : mesh c d (behead (x n)) <= fine (lambda n).
  have [_ +] := proj2_sig (cid (construct_x n)).
  rewrite -[X in (_ <= X)%E](@fineK _ (lambda n)); last first.
    admit.
  admit.
pose S_ n : R := variation c d f (behead (x n)).
pose V_ n : \bar R := \sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)|%:E +
     (\sum_(i < n) total_variation (A_ i) (B_ i) f).
pose CD_ n := merge <=%R [tuple c_ n i | i < n.+1] [tuple d_ n i | i < n.+1].
have sub_xcd n : subseq (CD_ n) (x n).
  admit.
have SV n : ((S_ n)%:E <= V_ n)%E.
  rewrite /S_ /V_.
  rewrite /variation.
  rewrite /=.
  admit.
set Vcd : \bar R := total_variation c d f.
have V_tv n : (V_ n <= Vcd)%E.
  admit.
have ac : a <= c.
  apply: lb_le_inf; last by move=> ? /Zab /=; rewrite in_itv/= => /andP[].
  apply/set0P/negP; move/eqP => Z0'.
  have := HZ; apply/negP.
  rewrite -leNgt le_eqVlt; apply/predU1P; left.
  by rewrite Z0' image_set0 measure0.
have db : d <= b.
  apply: ge_sup; last by move=> ? /Zab /=; rewrite in_itv/= => /andP[].
  apply/set0P/negP; move/eqP => Z0'.
  have := HZ; apply/negP.
  rewrite -leNgt le_eqVlt; apply/predU1P; left.
  by rewrite Z0' image_set0 measure0.
have cdbvf : bounded_variation c d f.
  apply: (bounded_variationl (ltW cd) db).
  apply: bounded_variationr ac _ bvf.
  by apply: ltW; exact: (lt_le_trans cd).
have Soo_tv : (S_ n)%:E @[n --> \oo] --> Vcd.
  have cdcf : {within `[c, d], continuous f}.
    apply: continuous_subspaceW cf.
    by apply: subset_itv; rewrite bnd_simp.
  have := lemma5 cd cdcf pcdx max_x lambda0.
  by rewrite /S_ /Vcd.
have Voo_V : V_ n @[n --> \oo] --> Vcd.
  apply: (squeeze_cvge _ Soo_tv); last first.
    exact: cvg_cst.
  apply: nearW => n.
  apply/andP; split.
    exact: SV.
  exact: V_tv.
have [n0 n00 tvV] : exists2 n0, (0 < n0)%N &
      forall n, (n0 <= n)%N -> (Vcd - alpha / 2 < V_ n)%E.
  have alpha20 : 0 < fine (alpha / 2).
    apply: fine_gt0; rewrite mule_gt0//=; last first.
      by rewrite inver ifF; exact/negP/negP.
    rewrite inver ifF; last exact/negP/negP.
    by rewrite lte_mul_pinfty ?measure_ge0 ?ltry.
  move: Voo_V.
  rewrite -{1}(@fineK _ Vcd); last first.
    by apply/bounded_variationP => //; exact: ltW.
  move/fine_cvg.
  move/(_ (ball (fine Vcd) (fine (alpha / 2))) (nbhsx_ballx _ _ alpha20)).
  move=> [n0 _ H].
  exists n0.+1 => //n n0n.
  have := H n (ltnW n0n).
  rewrite /ball/=.
  rewrite /ereal_ball/=.
  have Vcdoo : (Vcd < +oo)%E.
    rewrite -ge0_fin_numE; first by apply/bounded_variationP => //; exact: ltW.
    by apply: total_variation_ge0; exact: ltW.
  have Vn_fin : V_ n \is a fin_num.
    rewrite ge0_fin_numE; last first.
      apply: adde_ge0.
        exact: sume_ge0.
      apply: sume_ge0 => ? _.
      apply: total_variation_ge0.
      exact: ltW.
    exact: (le_lt_trans (V_tv n)).
  have al2fin : (alpha / 2)%E \is a fin_num.
    rewrite inver ifF; last exact/negP/negP.
    rewrite ge0_fin_numE.
      rewrite lte_mul_pinfty ?ltW//.
      exact: ltry.
    by rewrite mule_ge0 ?ltW.
  rewrite ger0_norm; last first.
    rewrite subr_ge0.
    rewrite fine_le//; last first.
      apply/bounded_variationP => //.
      exact: ltW.
  rewrite ltrBlDl -ltrBlDr.
  rewrite -fineB//; last first.
    by apply/bounded_variationP => //; exact: ltW.
  rewrite -lte_fin !fineK//.
  rewrite fin_numB; apply/andP; split => //.
  by apply/bounded_variationP => //; exact: ltW.
(* (4) *)
(* total_variationD? *)
have eq4 n : total_variation c d f =
  \sum_(i < n.+1) (H (d_ n i) - H (c_ n i))%:E +
   \sum_(i < n) (total_variation (A_ i) (B_ i) f).
  admit.
(* (5) *)
(* have eq5 n : (n0 <= n)%N -> \sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)|%:E. *)
(* (5.5) (between (5) and (6)) *)
have alphaH n : fine alpha < \sum_(i < n.+1) `|H (d_ n i) - H (c_ n i)|.
  rewrite /alpha.
  have -> : Z = ([set` Rhull Z] `\` cplt_hull Z).
   admit.
  rewrite setDE.
  apply: (@le_lt_trans _ _
    (fine (mu ((H @` [set` Rhull Z]) `&` (H @` (~` cplt_hull Z)))))).
    apply: fine_le.
    - admit.
    - admit.
    apply: le_outer_measure.
    exact: sub_image_setI.
  admit.
(*
rewrite addrAC ltrD2r.
move/(@lt_trans _ _ _ (fine alpha / 2)).
rewrite ltrBrDl -splitr; move/(_ alphaH).
*)
have : forall S : set R, measurable S -> S `<=` `[c, d] -> mu S = mu (S `&` cplt_hull Z).
  move=> S mS Scd.
  rewrite -[in LHS](setIidl Scd).
  rewrite -compact_Rhull//.
  have -> : [set` Rhull Z] = Z `|` cplt_hull Z.
    rewrite -(setUIDK [set` Rhull Z] Z); congr setU.
    apply: setIidr.
    exact: sub_Rhull.
  rewrite setIUr.
  rewrite measureU/=; last 3 first.
  - apply: sub_caratheodory.
    apply: measurableI => //.
    exact: compact_measurable.
  - apply: sub_caratheodory.
    apply: measurableI => //.
    apply: measurableD => //.
    exact: compact_measurable.
  - by rewrite setIACA setDIK setI0.
    rewrite -[RHS]add0e; congr +%E.
    apply/eqP; rewrite -measure_le0/=.
    rewrite -Z0.
    apply: le_outer_measure.
    exact: subIsetr.
(* (6.5) (between (6) and (7)) *)
pose abcd n (i : 'I_ n.+1) := [set k | `[A_ k, B_ k] `<=` `[c_ n i, d_ n i]].
set Uabcd := fun n i =>  \bigcup_(j in abcd n i) `[A_ j, B_ j]%classic. 
have itvfcd n (i : 'I_ n.+1) : is_interval (f @` `[c_ n i, d_ n i]).
  apply: (is_interval_image_cc cf).
  apply: subset_itv => //; rewrite bnd_simp.
    apply: (le_trans ac).
    case: i; case => /=; first by [].
    move=> i.
    rewrite ltnS => iltn.
    rewrite /c_/= nth_map_iota//.
    apply: le_trans (aleb n i).
    exact: clea.
  have := leq_ord i.
  rewrite leq_eqVlt => /predU1P[->|].
    by rewrite /d_ nth_rcons ifF ?if_same// size_map size_iota ltnn.
  move=> iltn.
  rewrite /d_ nth_rcons ifT ?size_map ?size_iota//.
  rewrite nth_map_iota//.
  apply: (le_trans (aleb n i)).
  exact: le_trans db.
have cdi n (i : 'I_ n.+1) : c_ n i <= d_ n i.
  admit.
(* ? *)
have cUabcd n i : closed (Uabcd n i).
    admit.
have hull_Uabcd n (i : 'I_ n.+1) : Rhull (Uabcd n i) = `[(c_ n i), (d_ n i)].
    admit.
have prop65 n : forall i : 'I_ n.+1, (`|f (d_ n i) - f (c_ n i)|%:E <=
  \sum_(n <= j <oo | `[< `[A_ j, B_ j] `<=` Uabcd n i >])
     oscillation f `[A_ j, B_ j])%E.
  move => i.
  apply: lime_ge.
    apply: ereal_nondecreasing_is_cvgn.
    apply: ereal_nondecreasing_series => k _ _.
    exact: oscillation_ge0.
  apply/nearW => k.
  have := @lemma4 _ (c_ n i) (d_ n i) (cdi n i) f (Uabcd n i)
                 (itvfcd n i) (cUabcd n i) (hull_Uabcd n i).
  move/andP => [le1 le2].
  apply: (le_trans le1).
  rewrite -(@setIidr _ [set` Rhull Z] `[c_ n i, d_ n i]%classic); last first.
    admit.
  rewrite -contiguous_intervals_Rhull; last by [].
  have -> : (mu [set f x | x in (\bigcup_k0 contiguous_intervals Z k0 `|` Z) `&` `[c_ n i, d_ n i]] = 0)%E.
    apply/eqP; rewrite eq_le; apply/andP; split; last first.
      exact: outer_measure_ge0.
    have <- : mu^*%mu (f @` Z) = 0.
      rewrite measurable_mu_extE; last first.
        apply: sub_caratheodory.
        apply: compact_measurable.
        apply: continuous_compact => //.
        exact: continuous_subspaceW cf.
      apply: lusinf => //.
      apply: sub_caratheodory.
      exact: compact_measurable.
    rewrite measurable_Rmu_extE/=; last first.
      admit.
(*
    apply: le_outer_measure.
    apply: image_subset.
    apply: bigcup_sub => j.
    rewrite /abcd/=.
    move/subset_trans; apply.
    rewrite /a_ /b_.
    apply: (subset_trans (contiguous_intervalsS _)).
    rewrite /a_.
*)
    admit.
  admit.
(*
rewrite -fine_invr -fineM//; last exact: fin_numV.
rewrite -lte_fin fineK; last first.
  apply: fin_numM => //; exact: fin_numV.
apply/negP.
rewrite -leNgt.

(* (7) *)
have : ((\sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)|)%:E <=
  \sum_(n <= i <oo) oscillation f `[A_ i, B_ i])%E.
  apply: lime_ge.
    apply: ereal_nondecreasing_is_cvgn.
    apply: ereal_nondecreasing_series => m _ _.
    exact: oscillation_ge0.
  near=> m.
  admit.
  (* have := lemma4. *)
move/le_trans; apply.
have ifcd : is_interval (f @` `[c, d]).
  by apply: (is_interval_image_cc cf); apply: subset_itv; rewrite bnd_simp;
    [exact: lb_le_inf|exact: ge_sup].
have clZ : closed Z by exact: compact_closed.
have hZE : Rhull Z = `[c, d].
  congr Interval.
  - rewrite ifT; last by apply/asboolP; exists a.
    congr BSide.
    apply/asboolP.
    admit.
  - rewrite ifT; last by apply/asboolP; exists b.
    congr BSide.
    apply/asboolPn.
    rewrite not_notE.
    admit.


have := (@lemma4 _ _ _ (ltW cd) f Z ifcd clZ hZE).
rewrite measurable_mu_extE/=; last first.
  apply: sub_caratheodory.
  apply: image_apply: measurable_imgage_
  admit.
have -> : mu (f @` Z) = 0.
  apply: lusinf => //=.
  apply: sub_caratheodory.
  exact: compact_measurable.
rewrite add0r.
move/andP=> [H].
move/(le_trans H).
have -> : (\big[+%E/0%R]_(0 <= i <oo)
      oscillation f `[contiguous_intervals1 Z i, contiguous_intervals2 Z i] =
  \big[+%E/0%R]_(0 <= i <oo) oscillation f
          `[contiguous_intervals1 Z (h1 i), contiguous_intervals2 Z (h1 i)])%E.
  admit.
rewrite /A_ /B_.
move/le_trans; apply.

admit.
*)
Admitted.

End lemma6_direct.

End lemma6_direct_new.

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
move : muZ_lty => /(@lebesgue_measure_Gdelta_approx R Z)[G [ZG oG Gnonincreasing muZ]].
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

Abort.

End lemma6_converse.
