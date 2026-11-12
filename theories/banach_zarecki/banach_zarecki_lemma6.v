From HB Require Import structures.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean perm finmap.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions contra cardinality.
From mathcomp Require Import reals topology normedtype ereal sequences derive.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import bz_mathcomp_extra bz_analysis_extra.
From mathcomp Require Import absolute_continuity banach_zarecki_lemma2.
From mathcomp Require Import banach_zarecki_lemma3 banach_zarecki_lemma5.
From mathcomp Require Import banach_zarecki_lemma4 (* for contiguous intervals *).
From mathcomp Require Import mesh oscillation interleave variation_extra
  diameter.

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

Module ListOfBounds.
Section list_of_bounds.
(* A is the (unordered) sequences of left bounds,
   B is the (unordered) sequence of right bounds *)
Context {R : realType} (A B : nat -> R).

(* unordered sequence of (left,right) bounds,
   the original indexed is recorded as a third component *)
Definition ABi n := [tuple ((A i, B i), nat_of_ord i) | i < n].

Lemma unzip2_ABi n : unzip2 (ABi n) = iota 0 n.
Proof.
by rewrite -val_enum_ord /ABi /unzip2 -[in LHS]map_comp/=; exact: eq_map.
Qed.

(* ordered sequence of (left,right) bounds,
   the third component records the original index *)
Definition left_lt {T1 T2} := fun x y : R * T1 * T2 => x.1.1 <= y.1.1.
Definition abi n := sort left_lt (ABi n).

Lemma nth_abiE def n i : (i < n)%N ->
  let p := nth (def, def, 0%N) (abi n) i in
  [/\ p.1.1 = A p.2, p.1.2 = B p.2 & (p.2 < n)%N].
Proof.
have abE : abi n =i ABi n.
  by apply: perm_mem; rewrite perm_sort; exact: perm_refl.
move=> ilen p.
have isize : (i < size (abi n))%N by rewrite size_tuple.
have : p \in ABi n by rewrite -(abE p); exact: mem_nth.
by move/mapP => [m _] ->; split => //=.
Qed.

(* ordered sequence of left bounds *)
Definition seq_a n := unzip1 (unzip1 (abi n)).

Lemma sorted_seq_a n : sorted <=%R (seq_a n).
Proof. by rewrite !sorted_map sort_sorted//= => ? ?/=; rewrite le_total. Qed.

(* ordered sequence of right bounds *)
Definition seq_b n := unzip2 (unzip1 (abi n)).

(* reordered indices *)
Definition seq_idx n := unzip2 (abi n).

Lemma seq_b_nth_idx d n :
  seq_b n = [seq nth d [tuple B i | i < n] i | i <- seq_idx n].
Proof.
rewrite /seq_b.
rewrite /unzip2.
rewrite -2!map_comp.
apply/eq_in_map => /= i abin.
move: abin.
rewrite /abi mem_sort => /mapP[j _ ->]/=.
by rewrite nth_mktuple.
Qed.

Let seq_idx_uniq n d (s : seq nat) :
  abi n = [seq nth (d, d, 0) (ABi n) i | i <- s] ->
  (forall k, k \in s -> (k < n)%N) ->
  seq_idx n = s.
Proof.
rewrite /seq_idx.
move/(congr1 unzip2) => -> sn.
apply/(@eq_from_nth _ 0); first by rewrite !size_map.
move=> i; rewrite !size_map => si.
do 2 rewrite (nth_map 0) ?size_map//.
have ? : ((s`_i)%R < n)%N by rewrite sn//; exact/mem_nth.
rewrite snd_map ?size_tuple//.
rewrite (nth_map 0) ?size_tuple//.
rewrite /ABi.
rewrite /tnth/=.
rewrite [X in (X`_ _).2](_ : _ = [seq (A i0, B i0, i0) | i0 <-iota 0 n]).
  by rewrite (map_comp (fun i0 => (A i0, B i0, i0))) -val_enum_ord.
rewrite (nth_map 0) ?size_iota//.
by rewrite nth_iota// K1.
Qed.

Lemma perm_seq_idx n : perm_eq (seq_idx n) (iota 0 n).
Proof.
set d : R := 0.
have [q H1 H2] := perm_iota_sort left_lt (d, d, 0) (ABi n).
have qn : forall k, k \in q -> (k < n)%N.
  move=> k.
  by rewrite (perm_mem H1) mem_iota leq0n/= add0n size_tuple card_ord.
move: H1; rewrite size_tuple.
apply: perm_trans.
by rewrite (seq_idx_uniq H2).
Qed.

Lemma mem_seq_idx_ub n i : i \in seq_idx n -> (i < n)%N.
Proof.
by rewrite (perm_mem (perm_seq_idx n)) mem_iota leq0n/= add0n.
Qed.

Lemma seq_b_idx n : seq_b n = [seq B i | i <- seq_idx n].
Proof.
rewrite (seq_b_nth_idx 0); apply/eq_in_map => i iq.
by rewrite (nth_mktuple _ _ (Ordinal (mem_seq_idx_ub iq))).
Qed.

End list_of_bounds.
End ListOfBounds.

Module OrderedBounds.
(* ordering of interval bounds *)
Section interval_bounds.
Context {R : realType} (A B : nat -> R).

Definition a_ def n := nth def (ListOfBounds.seq_a A B n).

Lemma a_default def m n : (m >= n)%N -> a_ def n m = def.
Proof. by move=> mn; rewrite /a_ nth_default// size_tuple. Qed.

Definition b_ def n := nth def (ListOfBounds.seq_b A B n).

Lemma b_default def m n : (m >= n)%N -> b_ def n m = def.
Proof. by move=> mn; rewrite /b_ nth_default// size_tuple. Qed.

Definition idx n := nth 0 (ListOfBounds.seq_idx A B n) : nat -> nat.

Lemma idx_bij n :
  exists idx_idxV : ('I_n -> 'I_n) * ('I_n -> 'I_n),
  [/\ (forall i (iltn1 : (i < n)%N), idx n i = idx_idxV.1 (Ordinal iltn1)),
      cancel idx_idxV.1 idx_idxV.2 &
      cancel idx_idxV.2 idx_idxV.1].
Proof.
have abE : (ListOfBounds.abi A B n) =i (ListOfBounds.ABi A B n).
  by apply: perm_mem; rewrite perm_sort; exact: perm_refl.
pose d : R := 0.
have idx_lt (i : 'I_ n) : (idx n i < n)%N.
  rewrite /idx /ListOfBounds.seq_idx.
  have isize : (i < size (ListOfBounds.abi A B n))%N by rewrite size_sort size_tuple.
  rewrite /idx.
  rewrite (nth_map (d, d, 0))//.
  have : nth (d, d, 0%N) (ListOfBounds.abi A B n) i \in ListOfBounds.ABi A B n.
    by rewrite -(abE _); exact: mem_nth.
  by move/mapP => [m _] ->/=; exact: ltn_ord.
pose idx_ord (i : 'I_n) := Ordinal (idx_lt i).
pose idx_inv (j : nat) := index j (ListOfBounds.seq_idx A B n).
have idx_inv_lt (j : 'I_n) : (idx_inv j < n)%N.
  rewrite /idx_inv.
  have : (size (ListOfBounds.seq_idx A B n) <= n)%N by rewrite size_tuple.
  move/ltn_leq_trans; apply.
  rewrite index_mem.
  rewrite (@perm_mem _ _ (iota 0 n)).
    exact: ListOfBounds.perm_seq_idx.
  by rewrite mem_iota leq0n/=.
pose idx_ord_inv j := Ordinal (idx_inv_lt j).
have idxE (i : 'I_n) : idx n i = idx_ord i by [].
exists (idx_ord, idx_ord_inv); split => //.
- move=> x/=.
  destruct n; first by case: x.
  rewrite -(inord_val (idx_ord x)) -(inord_val (idx_ord_inv _))/=.
  rewrite -[RHS](inord_val x); congr inord; rewrite /idx_inv inordK//.
  rewrite nthK//; last by rewrite inE size_tuple.
  rewrite (@perm_uniq _ _ (iota 0 n.+1)).
    have : perm_eq (ListOfBounds.abi A B n.+1) (ListOfBounds.ABi A B n.+1).
      by rewrite perm_sort.
    move/(perm_map snd)/perm_trans; apply.
    by rewrite -(ListOfBounds.unzip2_ABi A B).
  exact: iota_uniq.
- move=> x/=.
  destruct n; first by case: x.
  rewrite -(inord_val (idx_ord_inv x)) -(inord_val (idx_ord _))/=.
  rewrite -[RHS](inord_val x) ; congr inord; rewrite /idx_inv inordK//.
    exact: idx_inv_lt.
  apply: nth_index.
  suff -> : ListOfBounds.seq_idx A B n.+1 =i iota 0 n.+1.
    by rewrite mem_iota leq0n/=.
  rewrite -(ListOfBounds.unzip2_ABi A B).
  exact: eq_mem_map.
Qed.

Let abidE def n i :
  (a_ def n i, b_ def n i, idx n i) = nth (def, def, 0) (ListOfBounds.abi A B n) i.
Proof.
rewrite -(zip_unzip (ListOfBounds.abi A B n)) -(zip_unzip (unzip1 _)).
by rewrite !nth_zip ?size_zip ?size_map ?minnn.
Qed.

Lemma anth def n i : a_ def n i = (nth (def, def, 0) (ListOfBounds.abi A B n) i).1.1.
Proof. by rewrite -abidE. Qed.

Lemma bnth def n i : b_ def n i = (nth (def, def, 0) (ListOfBounds.abi A B n) i).1.2.
Proof. by rewrite -abidE. Qed.

Lemma idxE def n i : idx n i = (nth (def, def, 0) (ListOfBounds.abi A B n) i).2.
Proof. by rewrite -abidE. Qed.

Lemma a_lt_b def n i : (forall i, A i < B i) ->
  (i < n)%N -> a_ def n i < b_ def n i.
Proof.
move=> AB ni.
rewrite anth bnth.
have [-> -> _] := ListOfBounds.nth_abiE A B def ni.
exact/AB.
Qed.

Lemma a_le_b def n i : (forall i, A i < B i) ->
  a_ def n i <= b_ def n i.
Proof.
move=> AB.
have [ni|ni] := leqP n i; first by rewrite a_default// b_default.
exact/ltW/a_lt_b.
Qed.

Lemma perm_eq_AB_ab def n : perm_eq
  [tuple `]A i, B i[%classic | i < n]
  [tuple `]a_ def n i, b_ def n i[%classic | i < n].
Proof.
rewrite perm_sym; apply/(perm_iotaP set0).
exists (ListOfBounds.seq_idx A B n).
  rewrite size_tuple.
  rewrite /ListOfBounds.seq_idx.
  apply: (perm_trans (@perm_map _ _ snd (ListOfBounds.abi A B n) (ListOfBounds.ABi A B n) _)).
    by rewrite perm_sort.
  by rewrite -(ListOfBounds.unzip2_ABi A B).
apply: (@eq_from_nth _ set0); first by rewrite !size_tuple.
move=> j; rewrite size_tuple => jn.
rewrite (nth_mktuple _ _ (Ordinal jn))/= -map_comp.
rewrite (nth_map (def, def, 0)); first by rewrite size_tuple.
rewrite anth bnth.
have [-> -> idn] := ListOfBounds.nth_abiE A B def jn.
rewrite /comp/=.
by rewrite (nth_mktuple _ _ (Ordinal idn)).
Qed.

Let sort_keep_trivIset def n :
  trivIset [set: nat] (fun i => `]A i, B i[%classic) ->
  trivIset `I_n (fun i => `]a_ def n i, b_ def n i[%classic).
Proof.
move=> AB.
apply/trivIsetP => /= i j ni nj ij.
have := perm_eq_AB_ab def n.
move/(@perm_eq_trivIset_ord _ n _ _ `I_n).
move=> /(_ (@subset_refl _ `I_n)) => H.
have : trivIset `I_n (nth set0 [tuple `]A i0, B i0[%classic | i0 < n]).
  apply/trivIsetP => /= a b na nb ab.
  rewrite (nth_mktuple _ _ (Ordinal na)) (nth_mktuple _ _ (Ordinal nb))/=.
  by move/trivIsetP : AB; exact.
move/H => /trivIsetP => /(_ _ _ ni nj ij).
by rewrite (nth_mktuple _ _ (Ordinal ni))/= (nth_mktuple _ _ (Ordinal nj))/=.
Qed.

Let sorted_B_seq_idx' def n i j : (i < n)%N -> (j < n)%N ->
  (forall i, A i < B i) ->
  trivIset [set: nat] (fun i => `]A i, B i[%classic) ->
  a_ def n i <= a_ def n j ->
  b_ def n i <= b_ def n j.
Proof.
move=> ni nj /(@a_lt_b def n) a_b_ trab Ha_.
have [->//|ij] := eqVneq i j.
have H2 := a_b_ j nj.
rewrite leNgt; apply/negP => abs.
have /trivIsetP/(_ i j ni nj ij) := @sort_keep_trivIset def n trab.
pose x := (a_ def n j + b_ def n j) / 2.
rewrite -subset0 => /(_ x)[].
split.
  rewrite /= in_itv/= /x.
  apply/andP; split.
    rewrite (le_lt_trans Ha_)//.
    by rewrite midf_lt//.
  rewrite (le_lt_trans _ abs)//.
  by rewrite midf_le// ltW.
rewrite /= in_itv/= /x.
by rewrite !midf_lt.
Qed.

Lemma sorted_B_seq_idx n : (forall i, A i < B i) ->
  trivIset [set: nat] (fun i => `]A i, B i[%classic) ->
  sorted <=%R [seq B j | j <- ListOfBounds.seq_idx A B n].
Proof.
move=> a_b_ trab.
apply/(sortedP 0) => i.
have nn : size (ListOfBounds.seq_idx A B n) = n.
  by rewrite (perm_size (ListOfBounds.perm_seq_idx A B n)) size_tuple.
rewrite size_map [in X in X -> _]/= nn => ti.
rewrite (nth_map 0)//.
  by rewrite nn (leq_trans _ ti)//.
rewrite [in leRHS](nth_map 0)//.
  by rewrite nn.
have : a_ 0 n i <= a_ 0 n i.+1.
  have /sortedP := ListOfBounds.sorted_seq_a A B n.
  move/(_ 0 i).
  by rewrite !size_tuple => /(_ ti).
have ni : (i < n)%N by rewrite (leq_trans _ ti).
move/(@sorted_B_seq_idx' 0 n i i.+1 ni ti a_b_ trab).
rewrite /b_ (ListOfBounds.seq_b_nth_idx A B 0).
rewrite [in X in _ <= X -> _](nth_map 0)//.
  by rewrite nn.
rewrite [in X in X <= _ -> _](nth_map 0)//.
  by rewrite nn (leq_trans _ ti).
have nin : (((ListOfBounds.seq_idx A B n)`_i)%R < n)%N.
  rewrite (@ListOfBounds.mem_seq_idx_ub _ A B)//.
  apply/(nthP 0); exists i => //.
  by rewrite nn.
rewrite (nth_mktuple _ _ (Ordinal nin))/=.
have ni1n : (((ListOfBounds.seq_idx A B n)`_i.+1)%R < n)%N.
  rewrite (@ListOfBounds.mem_seq_idx_ub _ A B)//.
  apply/(nthP 0); exists i.+1 => //.
  by rewrite nn.
by rewrite (nth_mktuple _ _ (Ordinal ni1n))/=.
Qed.

Lemma sorted_seq_b n : (forall i, A i < B i) ->
  trivIset [set: nat] (fun i => `]A i, B i[%classic) ->
  sorted <=%R (ListOfBounds.seq_b A B n).
Proof.
by move=> AB trAB; rewrite ListOfBounds.seq_b_idx; exact: sorted_B_seq_idx.
Qed.

Lemma lb_A_a def c : c <= def ->
  (forall i, A i < B i) ->
  (forall i, c <= A i) ->
  (forall n i, c <= a_ def n i).
Proof.
move=> cdef AB cA_ n i.
have [ni|] := leqP n i; first by rewrite a_default.
move/(ListOfBounds.nth_abiE A B def) => [+ _ _].
rewrite -anth -idxE -/a_ => ->.
rewrite leNgt; apply/negP => Ac.
set x := ((A (idx n i)) + minr (B (idx n i)) c) / 2.
have : x < c.
  rewrite /x [in ltRHS](splitr c) mulrDl ltr_leD// ?ltr_pM2r ?ler_pM2r//.
  by rewrite ge_min lexx orbT.
apply/negP; rewrite -leNgt.
have : x \in `]A (idx n i), B (idx n i)[.
  rewrite in_itv/=; apply/andP; split.
    by rewrite midf_lt// lt_min AB Ac.
  rewrite (splitr (B _)) /x mulrDl ltr_leD// ?ltr_pM2r ?ler_pM2r//.
  by rewrite ge_min lexx.
rewrite in_itv/= => /andP[Ax _].
by rewrite (le_trans _ (ltW Ax)).
Qed.

Lemma up_B_b def d : def <= d ->
  (forall i, A i < B i) ->
  (forall i, B i <= d) ->
  (forall n i, b_ def n i <= d).
Proof.
move=> ddef AB B_d n i.
have [ni|] := leqP n i; first by rewrite b_default.
move/(ListOfBounds.nth_abiE A B def) => [_ + _].
rewrite -bnth -idxE -/b_ => ->.
rewrite leNgt; apply/negP => Bd.
set y := (maxr (A (idx n i)) d + B (idx n i)) / 2.
have : d < y.
  rewrite /y [in ltLHS](splitr d) mulrDl ler_ltD// ?ltr_pM2r ?ler_pM2r//.
  by rewrite le_max lexx orbT.
apply/negP; rewrite -leNgt.
have : y \in `]A (idx n i), B (idx n i)[.
  rewrite in_itv/=; apply/andP; split.
    rewrite (splitr (A _)) /y mulrDl ler_ltD// ?ltr_pM2r ?ler_pM2r//.
    by rewrite le_max lexx.
  by rewrite midf_lt// gt_max Bd AB.
by rewrite in_itv/= => /andP[_ /ltW] /le_trans; apply.
Qed.

Lemma b_le_a d :
  (forall i, A i < B i) ->
  trivIset [set: nat] (fun i => `]A i, B i[%classic) ->
  (forall i, B i <= d) ->
  forall n i, b_ d n i <= a_ d n i.+1.
Proof.
(* disjoint_contiguous_itvs *)
move=> AB trAB B_d.
move=> n i.
have [ni|iltn] := leqP n.-1 i.
  rewrite a_default.
    by move: ni; rewrite -subn1 leq_subLR add1n.
 exact: up_B_b.
rewrite leNgt; apply/negP => aibi.
(* TODO: take out, seems to depend only on sorted_b *)
have : `]a_ d n i, b_ d n i[ `&` `]a_ d n i.+1, b_ d n i.+1[ !=set0.
  rewrite [X in X !=set0](_ : _ = [set` `]a_ d n i.+1, b_ d n i[]).
    rewrite -set_itvI/=.
    rewrite /Order.meet/=.
    apply/set_itvP => r/=.
    congr (_ \in _).
    rewrite join_r.
      rewrite bnd_simp /a_.
      rewrite sorted_leq_nth ?inE//.
      - exact: le_trans.
      - exact: ListOfBounds.sorted_seq_a.
      - by rewrite size_tuple (leq_trans iltn)// leq_pred.
      - by rewrite size_tuple; destruct n.
    rewrite meet_l// bnd_simp.
    rewrite sorted_leq_nth ?inE//.
    - exact: le_trans.
    - exact: sorted_seq_b.
    - by rewrite size_tuple (leq_trans iltn)// leq_pred.
    - by rewrite !size_tuple; destruct n.
  exists ((a_ d n i.+1 + b_ d n i) / 2) => /=.
  by rewrite in_itv/= midf_lt//= midf_lt.
rewrite /a_ /b_ /ListOfBounds.seq_a /ListOfBounds.seq_b.
have /(@perm_eq_trivIset _ _ _ setT (subsetT _)) := perm_eq_AB_ab d n.
have triv_cgitv : trivIset [set: nat]
   [eta nth set0 [tuple `]A i1, B i1[%classic | i1 < n]].
  apply/trivIsetP.
  move=> j1 j2 _ _ => j12.
  have [nj1|j1n] := ltnP j1 n; last first.
    by rewrite nth_default ?size_tuple ?set0I.
  have [nj2|j2n] := ltnP j2 n; last first.
    by rewrite [X in _ `&` X]nth_default ?size_tuple ?setI0.
  rewrite (nth_mktuple _ _ (Ordinal nj1)) (nth_mktuple _ _ (Ordinal nj2))/=.
  by move/trivIsetP : trAB; exact.
move/(_ triv_cgitv).
move/trivIsetP.
move/(_ _ _ I I (negbT (ltn_eqF (ltnSn i)))).
have ni : (i < n)%N by rewrite (leq_trans iltn)// leq_pred.
have ni1 : (i.+1 < n)%N by rewrite -(@prednK n) ?(leq_ltn_trans _ ni).
rewrite (nth_mktuple _ _ (Ordinal ni))/= (nth_mktuple _ _ (Ordinal ni1))//=.
move=> H /set0P/negP.
exact/negP/eqP.
Qed.

Definition cd_ c d n := zip (c :: ListOfBounds.seq_b A B n) (rcons (ListOfBounds.seq_a A B n) d).

Let size_seq_cd {T} (mp : R * R -> T) c d n : size (map mp (cd_ c d n)) = n.+1.
Proof.
rewrite size_map size_zip size_rcons/= !size_map minnn.
by rewrite size_tuple.
Qed.

Definition seq_c c d n := unzip1 (cd_ c d n).

Definition seq_d c d n := unzip2 (cd_ c d n).

Definition c_ c d n j := nth d (seq_c c d n) j.

Lemma c_default c d m n : (m > n)%N -> c_ c d n m = d.
Proof. by move=> mn; rewrite /c_ nth_default// size_tuple. Qed.

Lemma cbE c d n j : c_ c d n j = if j == 0 then c else b_ d n j.-1.
Proof.
case: j => [|j/=].
  rewrite eqxx.
  rewrite /c_ /seq_c unzip1_zip//=.
  by rewrite size_rcons !size_map.
have [nj|jn] := leqP n.+1 j.+1.
  rewrite c_default//.
  rewrite bnth !nth_default ?size_seq_cd// size_tuple.
  by rewrite -ltnS.
rewrite /c_ /seq_c.
by rewrite unzip1_zip/=; first by rewrite size_rcons/= !size_map.
Qed.

Definition d_ c d n j := nth d (seq_d c d n) j.

Lemma d_default c d m n : (m > n)%N -> d_ c d n m = d.
Proof. by move=> mn; rewrite /d_ nth_default// size_tuple. Qed.

Lemma daE c d n j : d_ c d n j = a_ d n j.
Proof.
rewrite /d_ /seq_d.
rewrite unzip2_zip; first by rewrite size_rcons/= !size_map.
rewrite nth_rcons !size_tuple.
case: ifPn => [//|].
rewrite if_same /a_ -leqNgt => nj.
by rewrite -/(a_ _ _ _) a_default.
Qed.

End interval_bounds.
End OrderedBounds.

Lemma sum_oscillation_le_total_variation {R : realType} (a b : R) (f : R -> R) (A B : R^nat) :
  a < b ->
  {within `[a, b], continuous f} ->
  (forall i0 : nat, A i0 < B i0) ->
  let I i := `]A i, B i[%classic in
  trivIset [set: nat] I ->
  (forall n, `[A n, B n]%classic `<=` `[a, b]) ->
  (\sum_(i <oo) oscillation f (I i) <= total_variation a b f)%E.
Proof.
move=> ab cf AB I tI Iab.
apply: lime_le.
  apply: ereal_nondecreasing_is_cvgn => m n mn.
  apply: ereal_nondecreasing_series => // k _ _.
  by rewrite oscillation_ge0.
near=> n.
pose a_ := OrderedBounds.a_ A B b.
pose b_ := OrderedBounds.b_ A B b.
pose i_ i : set R := `](a_ n i), (b_ n i)[%classic.
apply/lee_addgt0Pr => /= e e0.
have ? : has_ubound (f @` `]a, b[).
  have [M Mcd Mmax] := EVT_max (ltW ab) cf.
  exists (f M) => _/= [r Ar <-].
  apply: Mmax.
  exact: subset_itv_oo_cc Ar.
have ? : has_lbound (f @` `]a, b[).
  have [m mcd mmin] := EVT_min (ltW ab) cf.
  exists (f m) => _/= [r Ar <-].
  apply: mmin.
  exact: subset_itv_oo_cc Ar.
have : forall i : 'I_n, exists xy, [/\ i_ i xy.1, i_ i xy.2, xy.1 < xy.2 &
    (`|f xy.1 - f xy.2|%:E > oscillation f (i_ i) - (e / n%:R)%:E)%E].
  move=> i.
  apply: oscillation_ub => //.
  - exact/OrderedBounds.a_lt_b.
  - apply: continuous_subspaceW cf.
    rewrite /a_ OrderedBounds.anth /b_ OrderedBounds.bnth.
    have [-> -> _] := ListOfBounds.nth_abiE A B b (ltn_ord i).
    exact: Iab.
  - rewrite divr_gt0//.
    by near: n; exact: nbhs_infty_gtr.
move/choice => [xy Hxy].
have [idx1 [idx_idx1 idx12K idx21K]] := OrderedBounds.idx_bij A B n.
rewrite big_mkord.
rewrite (_ : (\sum_(i < n) oscillation f (I i) = \sum_(i < n) oscillation f (i_ i))).
  rewrite [LHS](reindex_onto idx1.1 idx1.2)//=.
  rewrite big_mkcond/=.
  apply: eq_bigr => /= i _.
  rewrite idx12K eqxx.
  rewrite /i_ /I /=.
  rewrite /a_ OrderedBounds.anth.
  rewrite /b_ OrderedBounds.bnth.
  rewrite (and3proj1 (ListOfBounds.nth_abiE A B _ _))//.
  rewrite (and3proj2 (ListOfBounds.nth_abiE A B _ _))//.
  rewrite -OrderedBounds.idxE.
  destruct i.
  by rewrite -idx_idx1.
rewrite -leeBlDr//.
rewrite (@le_trans _ _ (\sum_(i < n) `|f (xy i).1 - f (xy i).2|%:E))//.
  rewrite [leLHS](_ : _ =
      (\sum_(i < n) (oscillation f (i_ i) - (e / n%:R)%:E)))%E.
    rewrite big_split/=; congr (_ + _).
    rewrite sumEFin.
    under eq_bigr do rewrite -mulNr.
    rewrite -big_distrl/=.
    rewrite big_const_ord/=.
    rewrite iter_addr_0.
    rewrite mulrnAl.
    rewrite -mulr_natr.
    rewrite -mulrA mulVf ?mulr1//.
    rewrite gt_eqF//.
    by near: n; exact: nbhs_infty_gtr.
  apply: lee_sum => /= k _.
  have [_ _ /= ?] := Hxy k.
  by move/ltW.
destruct n.
  by rewrite big_ord0 total_variation_ge0// ltW.
have ltn_div2 j : (j < n.+1.*2)%N -> (j./2 < n.+1)%N.
  by move=> jm; rewrite ltn_half_double.
pose s0 (i : 'I_n.+1.*2) : R :=
  let i' := Ordinal (ltn_div2 _ (ltn_ord i)) in
  if ~~ odd i then (xy i').1 else (xy i').2.
pose s := rcons [tuple s0 x | x < n.+1.*2] b.
rewrite (@le_trans _ _ (variation a b f s)%:E)//.
  rewrite /variation/=.
  rewrite big_mkord size_rcons size_map/= size_enum_ord.
  rewrite [in leRHS]big_ord_recl/=.
  rewrite sumEFin lee_fin.
  rewrite ler_wpDl//.
  rewrite -[leRHS](big_mkord xpredT (fun i => `|f (nth b s i.+1) - f (nth b s i)|)).
  rewrite [in leRHS](bigID [pred n | ~~ odd n] xpredT)//=.
  rewrite ler_wpDr//.
    by rewrite sumr_ge0//.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  transitivity (
      \sum_(0 <= i < n.+1) `|f (nth b s i.*2.+1) - f (nth b s i.*2)| ); last first.
    by rewrite (bigop_mul2_even _ (fun i => `|f (nth b s i.+1) - f (nth b s i)|)).
  rewrite big_mkord.
  apply: eq_bigr => i _.
  rewrite /s.
  have H1 : (i.*2.+1 < n.+1.*2)%N.
    rewrite doubleS ltnS.
    rewrite ltnS.
    by rewrite leq_double -ltnS.
  rewrite !nth_rcons/= size_map size_enum_ord H1.
  have H2 : (i.*2 < n.+1.*2)%N.
    by rewrite ltn_double.
  rewrite H2.
  rewrite (nth_map (Ordinal H1))/=.
    by rewrite (size_enum_ord n.+1.*2).
  rewrite (nth_ord_enum _ (Ordinal H1)).
  rewrite (nth_map (Ordinal H2))/=.
    by rewrite size_enum_ord.
  rewrite (nth_ord_enum _ (Ordinal H2)).
  rewrite distrC.
  congr (`| f _ - f _ |).
    rewrite /s0 /= negbK.
    rewrite odd_double/=.
    congr ((xy _).2).
    apply/val_inj => /=.
    by rewrite uphalf_double.
  rewrite /s0 /= odd_double/=.
  congr ((xy _).1).
  apply/val_inj => /=.
  by rewrite (half_bit_double _ false)//.
apply: variation_le_total_variation.
  apply: path_ltW.
  rewrite /s.
  rewrite rcons_path; apply/andP; split.
    apply/(pathP b) => i.
    rewrite size_tuple => ni.
    have [i0|i0] := eqVneq i 0.
      rewrite i0/=.
      rewrite (@lt_le_trans _ _ (xy ord0).1)//.
        have [+ _ _ _] := Hxy ord0.
        rewrite /i_/= in_itv/= => /andP[+ _].
        apply: le_lt_trans.
        rewrite /a_ OrderedBounds.anth.
        rewrite (and3proj1 (ListOfBounds.nth_abiE _ _ _ _))//.
        rewrite -OrderedBounds.idxE.
        have /= := Iab (OrderedBounds.idx A B n.+1 0).
        have /itvP ->// : A (OrderedBounds.idx A B n.+1 0) \in `[a, b].
        rewrite inE.
        apply: (Iab (OrderedBounds.idx A B n.+1 0)) => /=.
        rewrite in_itv/= lexx/=.
        by rewrite ltW.
      rewrite (nth_map ord0)//.
        by rewrite size_enum_ord//.
      rewrite /s0/=.
      rewrite (@nth_ord_enum n.+1.*2 ord0 ord0)//=.
      rewrite (_ : Ordinal _ = ord0)//.
      exact/val_inj.
    rewrite (nth_map ord0) ?size_tuple//=.
    rewrite (nth_ord_enum ord0 (Ordinal ni))/=.
   rewrite nth_cons lt0n i0.
    rewrite (nth_map ord0).
      rewrite (@leq_trans i)//.
        by rewrite prednK// lt0n.
      by rewrite size_enum_ord ltnW.
    rewrite (nth_ord_enum ord0 (Ordinal (leq_ltn_trans (leq_pred i) ni)))/=.
    rewrite /s0/=.
    have [oddi1|eveni1] := boolP (odd i.-1) => /=.
      rewrite (_ : odd i = odd i.-1.+1).
        by rewrite prednK// lt0n.
      rewrite oddS oddi1//=.
      rewrite (@le_lt_trans _ _ (b_ n.+1 i.-1./2))//.
        set i1 := Ordinal _.
        have [_ + _ _] := Hxy i1.
        rewrite /i_/= in_itv/= => /andP[_].
        by move/ltW => /le_trans; exact.
      have [+ _ _ _] := Hxy (Ordinal (ltn_div2 i (ltn_ord (Ordinal ni)))).
      rewrite /= /i_/= in_itv/= => /andP[+ _].
      apply: le_lt_trans.
      rewrite /b_ /a_.
      have -> : b = sup `[a, b] by rewrite sup_itvcc// ltW.
      rewrite (_ : i./2 = i.-1./2.+1).
        rewrite -{1}(@prednK i) ?lt0n//.
        rewrite -uphalfE.
        rewrite -addn1 addnC.
        by rewrite -/(nat_of_bool true) -oddi1 -uphalf_half.
      rewrite (sup_itvcc (ltW ab))//.
      apply: OrderedBounds.b_le_a => // j.
      suff: B j \in `[a, b] by move/itvP ->.
      by apply/(Iab j); rewrite /= bound_itvE ltW.
    rewrite (_ : odd i = odd i.-1.+1).
      by rewrite prednK// lt0n.
    rewrite oddS eveni1/=.
    have -> : Ordinal (ltn_div2 i.-1 (ltn_ord (Ordinal (leq_ltn_trans (leq_pred i) ni)))) =
        Ordinal (ltn_div2 i (ltn_ord (Ordinal ni))).
      apply/val_inj => /=.
      have := uphalf_half i.-1.
      rewrite (negbTE eveni1) add0n => <-.
      by rewrite uphalfE prednK// lt0n.
    exact: (and4proj3 (Hxy _)).
  pose n1 := @ord_max n.
  rewrite (@le_lt_trans _ _ (xy n1).2)//.
    rewrite [leLHS](_ : _ = s0 ord_max).
      rewrite -nth_last /s0.
      rewrite size_map size_enum_ord.
      rewrite ifF.
        by rewrite /= odd_double /=.
      rewrite (nth_map ord0) ?size_tuple ?predn1K//.
      have tmp : (n.+1.*2.-1 < n.+1.*2)%N.
        by rewrite prednK//.
      rewrite (nth_ord_enum ord0 (Ordinal tmp))//.
      rewrite [~~ _]/= odd_double.
      congr (xy _).2.
      apply/val_inj => /=.
      by rewrite uphalf_half odd_double add0n.
    rewrite /s0.
    rewrite ifF.
      by rewrite /= odd_double.
    rewrite (_ : Ordinal _ = n1)//.
    apply/val_inj => //=.
    rewrite uphalf_half odd_double add0n//=.
    by rewrite -[RHS](half_bit_double _ false)// add0n.
  have [_ + _ _] := Hxy n1.
  rewrite /i_/= in_itv/= => /andP[_].
  move/lt_le_trans; apply.
  rewrite /b_ OrderedBounds.bnth.
  rewrite (and3proj2 (ListOfBounds.nth_abiE _ _ _ _))//.
  rewrite -OrderedBounds.idxE.
  have /= := Iab (OrderedBounds.idx A B n.+1 n1).
  have : B (OrderedBounds.idx A B n.+1 n1) \in `[a, b].
    rewrite inE.
    apply: (Iab (OrderedBounds.idx A B n.+1 n1)) => /=.
    by rewrite bound_itvE// ltW.
  by move=> /itvP ->.
by rewrite /s last_rcons.
Unshelve. all: end_near. Qed.

(*
Z : set R
contiguous_itvs Z :
[c   = c_0, d_0 = a_0]  ]a_0, b_0[
[c_1 = b_0, d_1 = a_1]  ]a_1, b_1[
[c_2 = b_1, d_2 = a_2]  ]a_2, b_2[
...
[c_n.-1 = b_n.-2, d_n.-1 = a_n.-1] ]a_n.-1, b_n.-1[
[c_n    = b_n.-1, d_n = a_n]       ]a_n, b_n[
[c_n.+1 = b_n, d_n.+1 = d]
*)

Module ContItvs.
Section contiguous_itvs.
Context {R : realType} (Z : set R) (a b : R) (lbZ : has_lbound Z)
  (ubZ : has_ubound Z).
Let supp := contiguous_itvs_support Z.
Variable h1 : {splitbij [set: nat] >-> supp}.
Let A n := contiguous_itvs1 Z (h1 n).
Let B n := contiguous_itvs2 Z (h1 n).

Let seq_b := ListOfBounds.seq_b A B.

Let A_lt_B i : A i < B i.
Proof.
apply: contiguous_itvs1_lt_contiguous_itvs2 => //.
have [+ _ _] := @bij _ _ _ _ h1.
by rewrite /set_fun => /(_ i Logic.I).
Qed.

Lemma trivIsetAB : trivIset [set: nat] (fun i => `]A i, B i[%classic).
Proof.
apply/trivIsetP => i j _ _ ij.
have /trivIsetP := trivIset_contiguous_itvs lbZ ubZ.
move=> /(_ (h1 i) (h1 j)); apply => //.
contra: ij => ij.
have [_ + _] := @bij _ _ _ _ h1.
by apply => //; rewrite in_setT.
Qed.

Let c := inf Z.
Let d := sup Z.
Let a_ := OrderedBounds.a_ A B d.
Let b_ := OrderedBounds.b_ A B d.

Let ABcd i : `]A i, B i[ `<=` `[c, d].
Proof.
rewrite -contiguous_ooitv//.
apply: (@subset_trans  _ [set` Rhull Z]).
  apply: (subset_trans (@contiguous_itvsS _ _ _)).
  exact: cplt_hull_subset_Rhull.
apply: subset_itv.
  rewrite ifT; first exact/asboolP.
  by have [_|_] := boolP `[< (Z (inf Z)) >]; rewrite bnd_simp.
rewrite ifT; first exact/asboolP.
by have [_|_] := boolP `[< (Z (sup Z)) >]; rewrite bnd_simp.
Qed.

Lemma inf_le_a : Z !=set0 -> forall n i, c <= a_ n i.
Proof.
move=> Z0.
have [|subZ] := pselect (is_subset1 Z); last first.
  apply: OrderedBounds.lb_A_a => //.
    exact: has_bound_inf_sup.
  move=> i; rewrite -/c.
  suff: `[c, d]%classic (A i) by rewrite /= => /itvP[->].
  have /closureS := @ABcd i.
  rewrite closure_neitv_oo// closure_neitv_cc//.
    exact: has_bound_not_subset1_inf_sup.
  by apply => /=; rewrite bound_itvE ltW.
move/is_subset1P => -[Z0'|[z Zz]].
  absurd.
  by apply/eqP/set0P : Z0'.
have := @ABcd O.
rewrite /c /d Zz sup1 inf1 set_itv1 => /subset_set1[abs|abs].
  absurd : abs.
  apply/set0P; exists ((A 0 + B 0) / 2).
  by rewrite /= !in_itv/= !midf_lt.
absurd.
suff: open `]A 0, B 0[%classic.
  rewrite abs.
  exact: set1_not_open.
exact: itv_open.
Qed.

Lemma b_le_sup : Z !=set0 -> forall n i, b_ n i <= d.
Proof.
move=> Z0.
have [|subZ] := pselect (is_subset1 Z); last first.
  move=> n i.
  apply: OrderedBounds.up_B_b => // i0; rewrite -/c.
  suff: `[c, d]%classic (B i0) by rewrite /= => /itvP[->].
  have /closureS := @ABcd i0.
  rewrite closure_neitv_oo// closure_neitv_cc//.
    exact: has_bound_not_subset1_inf_sup.
  by apply => /=; rewrite bound_itvE ltW.
move/is_subset1P => -[Z0'|[z Zz]].
  absurd.
  by apply/eqP/set0P : Z0'.
have := @ABcd O.
rewrite /c /d Zz sup1 inf1 set_itv1 => /subset_set1[abs|abs].
  absurd : abs.
  apply/set0P; exists ((A 0 + B 0) / 2).
  by rewrite /= !in_itv/= !midf_lt.
absurd.
suff: open `]A 0, B 0[%classic.
  rewrite abs.
  exact: set1_not_open.
exact: itv_open.
Qed.

Lemma inf_le_b n i : Z !=set0 -> c <= b_ n i.
Proof.
move=> Z0; rewrite (@le_trans _ _ (a_ n i)) ?inf_le_a//.
by rewrite OrderedBounds.a_le_b.
Qed.

Lemma b_le_a : compact Z -> Z !=set0 -> forall n i, b_ n i <= a_ n i.+1.
Proof.
move=> compactZ Z0 n i.
apply (@OrderedBounds.b_le_a _ _ _ d) => //; first exact: trivIsetAB.
move=> j.
apply: sup_contiguous_itvs2 => //.
have : h1 j \in supp.
  apply/mem_set.
  have [+ _ _] := @bij _ _ _ _ h1.
  exact.
by rewrite inE.
Qed.

Lemma a_le_sup : Z !=set0 -> forall n i, a_ n i <= d.
Proof.
move=> Z0 n i.
rewrite (@le_trans _ _ (b_ n i)) ?b_le_sup//.
by rewrite OrderedBounds.a_le_b.
Qed.

Local Notation c_ := (OrderedBounds.c_ A B c d).
Local Notation d_ := (OrderedBounds.d_ A B c d).

Lemma inf_le_d : Z !=set0 -> forall n i, c <= d_ n i.
Proof. by move=> Z0 n i; rewrite OrderedBounds.daE inf_le_a. Qed.

Lemma d_le_sup : Z !=set0 -> forall n i, d_ n i <= d.
Proof. by move=> Z0 n i; rewrite OrderedBounds.daE a_le_sup. Qed.

Lemma c_le_d : compact Z -> Z !=set0 -> forall n i, c_ n i <= d_ n i.
Proof.
move=> compactZ Z0 n i.
rewrite OrderedBounds.cbE OrderedBounds.daE.
by case: i => /=[|i]; [exact: inf_le_a|exact: b_le_a].
Qed.

Lemma c_le_sup : Z !=set0 -> forall n i, c_ n i <= d.
Proof.
move=> Z0 n i.
rewrite OrderedBounds.cbE; case: ifPn => [_|i0]; first exact: has_bound_inf_sup.
exact: b_le_sup.
Qed.

Lemma inf_le_c n i : Z !=set0 -> c <= c_ n i.
Proof.
move=> Z0; rewrite OrderedBounds.cbE; case: ifPn => // i0.
rewrite (@le_trans _ _ (a_ n i.-1)) ?inf_le_a//.
by rewrite OrderedBounds.a_le_b.
Qed.

Lemma sorted_c n : Z !=set0 -> sorted <=%R (OrderedBounds.seq_c A B c d n).
Proof.
move=> Z0; apply/(sortedP d) => j; rewrite size_tuple ltnS => jn.
rewrite -!/(c_ _ _) !OrderedBounds.cbE -/b_/=.
case: ifPn => j0.
  exact: inf_le_b.
apply/le_sorted_leq_nth => //=; rewrite ?inE/= ?size_tuple//.
- by apply: OrderedBounds.sorted_seq_b => //; exact: trivIsetAB.
- by rewrite prednK ? lt0n// ltnW.
- by rewrite leq_pred.
Qed.

Lemma sorted_d n : Z !=set0 -> sorted <=%R (OrderedBounds.seq_d A B c d n).
Proof.
move=> Z0; apply/(sortedP d) => j; rewrite size_tuple ltnS => jn.
rewrite -!/(d_ _ _) !OrderedBounds.daE -/a_.
have [{}jn|j1n] := eqVneq j.+1 n.
  by rewrite jn [leRHS]OrderedBounds.a_default// a_le_sup.
apply/le_sorted_leq_nth => //=; rewrite ?inE/= ?size_tuple//.
  exact: ListOfBounds.sorted_seq_a.
by rewrite ltn_neqAle j1n.
Qed.

Lemma Zcd n : c < d -> compact Z -> Z !=set0 ->
  Z `<=` \bigcup_(i < n.+1) `[c_ n i, d_ n i]%classic.
Proof.
move=> cd cZ Z0.
suff : [set` Rhull Z] `\` \bigcup_(i < n.+1) `[c_ n i, d_ n i]%classic
  `<=` cplt_hull Z.
  rewrite -subset_setCS//; first  exact: sub_Rhull.
  move=> x [i iltn2]/=.
  rewrite compact_Rhull// !in_itv/= -/c -/d.
  move=> /andP[cx xd]; apply/andP; split.
    apply: le_trans cx.
    rewrite OrderedBounds.cbE; case: i iltn2 xd => //= i.
    rewrite ltnS => iltn1 _.
    apply: (@le_trans _ _ (OrderedBounds.a_ A B d n i)).
      exact: inf_le_a.
    exact: OrderedBounds.a_le_b.
  by rewrite (le_trans xd)// d_le_sup.
apply: (@subset_trans _ (\bigcup_(i < n) `]a_ n i, b_ n i[%classic)).
  destruct n.
    rewrite 2!bigcup_mkord big_ord0 big_ord_recl/= big_ord0 setU0.
    rewrite OrderedBounds.cbE/=.
    rewrite OrderedBounds.daE/=.
    rewrite OrderedBounds.a_default//.
    rewrite compact_Rhull//.
    by rewrite setDv.
  move=> x [hZx].
  rewrite {1}/bigcup/= exists2E; move/forallNP => ncdx.
  have has_b : has (> x) (seq_b n.+1).
    apply/(has_nthP d).
    exists n; first by rewrite size_tuple.
    have := ncdx n.+1.
      rewrite ltnSn => /andP; rewrite andTb.
      rewrite in_itv/= negb_and -!ltNge => /orP[|].
      by rewrite OrderedBounds.cbE.
    rewrite OrderedBounds.daE.
    rewrite -/(a_ n.+1 n.+1) /a_ OrderedBounds.a_default//.
    rewrite ltNge => /negP.
    by have := hZx; rewrite compact_Rhull//= in_itv/= => /andP[].
  (* x < b_ n k となる最小のk (remark: sorted <=%R (seq_b n)) *)
  pose k := find (> x) (seq_b n.+1).
  have kn1 : (k < n.+1)%N  by move: has_b; rewrite has_find size_tuple.
  exists k => //=.
  rewrite in_itv/=; apply/andP; split; last by rewrite nth_find.
  have [k0|] := eqVneq k 0.
    rewrite k0 ltNge; apply/negP => xan0.
    apply: (ncdx 0); split => //; rewrite in_itv OrderedBounds.cbE OrderedBounds.daE/=.
    apply/andP; split => //.
    by move: hZx; rewrite compact_Rhull//= in_itv/= => /andP[].
  rewrite -leqn0 -ltnNge => k0.
  rewrite ltNge; apply/negP => xank.
  apply: (ncdx k); split; first by rewrite ltnS ltnW.
  rewrite in_itv/= OrderedBounds.cbE OrderedBounds.daE ifF.
    by apply/negP/negP; rewrite -leqn0 -ltnNge.
  apply/andP; split => //.
  rewrite leNgt; apply/negP/negP; apply: negbT.
  apply: before_find; rewrite -/k.
  by rewrite ltn_predL.
rewrite cplt_hull_contiguous_itvs//; first exact: compact_closed.
rewrite bigcup_contiguous_itvs_support.
rewrite (_: \bigcup_(k in supp) contiguous_itvs Z k =
            \bigcup_k contiguous_itvs Z (h1 k)).
  have [funh1 injh1 surjh1] := @bij _ _ _ _ h1.
  by rewrite (reindex_bigcup _ _ _ _ funh1 surjh1).
move=> x [i /= iltn].
rewrite /a_ /b_ OrderedBounds.anth OrderedBounds.bnth.
have [-> -> _] := ListOfBounds.nth_abiE A B d iltn.
rewrite -!OrderedBounds.idxE => xAB.
exists (OrderedBounds.idx A B n i) => //.
by rewrite contiguous_ooitv.
Qed.

Lemma citvScd_tmp n x : compact Z -> Z !=set0 ->
  contiguous_itvs Z (h1 n) x ->
  forall m, (m <= n)%N ->
  exists2 p, (p < m.+1)%N & x \in `[c_ m p, d_ m p].
Proof.
move=> cZ X0 xn m nm.
have hasxd : has (> x) (OrderedBounds.seq_d A B c d m).
  apply/hasP.
  exists d.
    have {1}<- : d_ m m = d.
      by rewrite OrderedBounds.daE OrderedBounds.a_default.
    by rewrite mem_nth// size_tuple.
  have := xn.
  move/contiguous_itvsS.
  by move/cplt_hull_lt_sup => /(_ ubZ).
set p := find (> x) (OrderedBounds.seq_d A B c d m).
have pE : p = find (> x) (OrderedBounds.seq_d A B c d m) by [].
have pltm2 : (p < m.+1)%N.
  rewrite -(size_tuple (OrderedBounds.seq_d A B c d m)).
   by rewrite -has_find.
exists p => //.
rewrite in_itv/=; apply/andP; split; last first.
  exact/ltW/nth_find.
case: p pE pltm2.
  rewrite OrderedBounds.cbE/=.
  have := xn.
  move/contiguous_itvsS.
  move/cplt_hull_subset_Rhull.
  by rewrite compact_Rhull//= => /itvP ->.
move=> p pE p1ltm2.
rewrite leNgt; apply/negP.
rewrite OrderedBounds.cbE/= OrderedBounds.bnth.
have pltm1 : (p < m)%N.
  by rewrite ltnS in p1ltm2.
have : d_ m p < x.
  rewrite ltNge le_eqVlt; apply/negP => /predU1P.
  apply/not_orP; split.
    rewrite OrderedBounds.daE => xamp.
    move: (xn).
    rewrite xamp.
    rewrite contiguous_ooitv//= in_itv/= => /andP[_ ].
    rewrite -/(B _).
    rewrite /a_.
    rewrite OrderedBounds.anth.
    have [-> _] := ListOfBounds.nth_abiE A B d pltm1.
    rewrite -OrderedBounds.idxE => idxmpm1 AmpBn.
    have := @disjoint_contiguous_itvs _ Z.
    move/trivIsetP/(_ (h1 (OrderedBounds.idx A B m p)) (h1 n)).
    move/(_ I I).
    (* lemma *)
    have pn : h1 (OrderedBounds.idx A B m p) != h1 n.
      have [_ injh1 _] := @bij _ _ _ _ h1.
      apply/eqP.
      move/injh1; rewrite inE/= => /(_ I I).
      apply/eqP.
      rewrite neq_ltn; apply/orP; left.
      by rewrite (ltn_leq_trans idxmpm1)// ltnW.
    move/(_ pn).
    move/eqP; apply/negP/set0P.
    have : A n < B (OrderedBounds.idx A B m p).
      apply: (@lt_trans _ _ x).
        move: xn.
        by rewrite contiguous_ooitv//= => /itvP ->.
      rewrite xamp /a_ OrderedBounds.anth.
      have [-> _ _] := ListOfBounds.nth_abiE A B d pltm1.
      rewrite -OrderedBounds.idxE.
      apply: contiguous_itvs1_lt_contiguous_itvs2 => //.
      suff: supp (h1 (OrderedBounds.idx A B m p)) by [].
      have [+ _ _] := @bij _ _ _ _ h1.
      by apply.
    exists ((A (OrderedBounds.idx A B m p) + B n) / 2); split.
      rewrite contiguous_ooitv//= in_itv/=.
      rewrite midf_lt//=.
      rewrite -/(B (OrderedBounds.idx A B m p)) mulrDl.
      rewrite (splitr (B (OrderedBounds.idx A B m p))).
      apply: ltr_leD.
        by rewrite ltr_pM2r.
      rewrite ler_pM2r//.
      rewrite leNgt; apply/negP => mpn.
      have := @disjoint_contiguous_itvs _ Z.
      move/trivIsetP/(_ (h1 (OrderedBounds.idx A B m p)) (h1 n)) => /=.
      move/(_ I I pn)/eqP.
      apply/negP/set0P.
      exists ((A (OrderedBounds.idx A B m p) + B (OrderedBounds.idx A B m p)) / 2); split.
        rewrite contiguous_ooitv//= in_itv/=; rewrite !midf_lt//.
        apply: contiguous_itvs1_lt_contiguous_itvs2 => //.
        suff: supp (h1 (OrderedBounds.idx A B m p)) by [].
        have [+ _ _] := @bij _ _ _ _ h1.
        exact.
      rewrite contiguous_ooitv//= in_itv/=; apply/andP; split.
        rewrite -/(A n) (splitr (A n)) mulrDl ltrD//.
          rewrite ltr_pM2r//.
          move: xn.
          rewrite contiguous_ooitv//= in_itv/= => /andP[+ _].
          rewrite xamp /a_ OrderedBounds.anth.
          by have [-> _ _] := ListOfBounds.nth_abiE A B d pltm1; rewrite -OrderedBounds.idxE.
        by rewrite ltr_pM2r.
      rewrite -/(B n) (splitr (B n)) mulrDl.
      by apply: ltrD; rewrite ltr_pM2r.
    rewrite contiguous_ooitv//= in_itv/=; apply/andP; split.
      rewrite -/(A n) (splitr (A n)) mulrDl.
      apply: ltrD.
        rewrite ltr_pM2r//.
        move: xn.
        rewrite contiguous_ooitv//= in_itv/= => /andP[+ _].
        rewrite xamp /a_ OrderedBounds.anth.
        by have [-> _ _] := ListOfBounds.nth_abiE A B d pltm1; rewrite -OrderedBounds.idxE.
      by rewrite ltr_pM2r.
    rewrite -/(B n) [in ltRHS](splitr (B n)) mulrDl.
    rewrite ltrD2r.
    by rewrite ltr_pM2r.
  apply/negP/negPf.
  apply: before_find.
  by rewrite pE.
rewrite OrderedBounds.daE OrderedBounds.anth.
have [-> -> +] := ListOfBounds.nth_abiE A B d pltm1.
rewrite -OrderedBounds.idxE => idxltm1 Apx xBp.
have np : h1 n != h1 (OrderedBounds.idx A B m p).
  (* lt_le_trans pltm1 nm *)
  have [_ injh1 _] := @bij _ _ _ _ h1.
  apply/eqP; move/injh1; rewrite inE/= => /(_ I I).
  move/eqP.
  rewrite gtn_eqF//.
  by rewrite (ltn_leq_trans idxltm1)// ltnW.
have := @disjoint_contiguous_itvs _ Z.
move/trivIsetP/(_ (h1 n) (h1 (OrderedBounds.idx A B m p))).
move/(_ I I np).
apply/eqP/set0P; exists x; split => //.
by rewrite contiguous_ooitv//= in_itv/= Apx xBp.
Qed.

Lemma hullZ_abcd n : c < d -> compact Z -> Z !=set0 ->
  [set` Rhull Z] =
  \bigcup_(i < n.+1) `[c_ n i, d_ n i]%classic `|`
  \bigcup_(i < n) `]a_ n i, b_ n i[%classic.
Proof.
move=> cd cZ Z_nonempty.
have clZ : closed Z by apply: compact_closed.
rewrite -(contiguous_itvs_Rhull clZ).
pose h := h1^-1%FUN.
have h1h : {in supp, cancel h h1} by exact: funK.
apply/seteqP; split => [r|r].
- move=> [|].
  + move=> [i _ Zir].
    have [hin|hin] := boolP (i \in map h1 (iota 0 n)).
      right.
      have [[idx_ord idx_ord_inv] /= [idx_ordE can_ord_inv can_inv_ord]]
        := OrderedBounds.idx_bij A B n.
      rewrite -/OrderedBounds.idx in idx_ordE.
      have hi_lt : (h i < n)%N.
        move: hin.
        rewrite -{1}(h1h i).
         by rewrite inE; exists r.
       rewrite mem_map.
         move=> t0 t1.
         have [_ + _]:= @bij _ _ _ _ h1.
         by apply => //; rewrite inE.
       by rewrite mem_iota add0n => /andP[].
      exists (idx_ord_inv (Ordinal hi_lt)).
        by rewrite /=.
      rewrite /a_ OrderedBounds.anth /b_ OrderedBounds.bnth.
      have []// := @ListOfBounds.nth_abiE _ A B d n (idx_ord_inv (Ordinal hi_lt)).
      move=> -> ->; rewrite -OrderedBounds.idxE.
      rewrite -/OrderedBounds.idx.
      rewrite !idx_ordE.
      rewrite [X in (idx_ord X < _)%N](_ : _ = idx_ord_inv (Ordinal hi_lt)).
        exact: val_inj.
      rewrite [X in A (idx_ord X)] (_ : _ = idx_ord_inv (Ordinal hi_lt)).
        exact: val_inj.
      rewrite [X in B (idx_ord X)] (_ : _ = idx_ord_inv (Ordinal hi_lt)).
        exact: val_inj.
      rewrite can_inv_ord/=.
      move=> _.
      move: (Zir).
      rewrite (contiguous_ooitv ubZ lbZ).
      rewrite /A /B.
      rewrite !h1h//.
      by rewrite inE; exists r.
    left.
    have ih1hi : i = h1 (h i) by rewrite h1h// inE; exists r.
    have nhi : (n <= h i)%N.
      move: hin.
      rewrite {1}ih1hi mem_map.
        move=> x y.
        have/set_bij_inj := @bij _ _ _ _ h1.
        by apply; rewrite !inE.
      by rewrite mem_iota add0n leq0n/= -ltnNge ltnS.
    rewrite ih1hi in Zir.
    have [k kn2 rcd] := citvScd_tmp cZ Z_nonempty Zir nhi.
    by exists k.
  + move=> Zr.
    left.
    exact: Zcd.
- move=> [[i _]|[i _]]; rewrite (contiguous_itvs_Rhull clZ).
  + rewrite /= in_itv/= => /andP[cir rdi].
    rewrite compact_Rhull// in_itv/=; apply/andP; split.
      by rewrite (le_trans _ cir)// inf_le_c.
    by rewrite (le_trans rdi)// d_le_sup.
  + rewrite /= in_itv/= => /andP[/ltW air /ltW rbi].
    rewrite compact_Rhull// in_itv/=; apply/andP; split.
      by rewrite (le_trans _ air)// inf_le_a.
    by rewrite (le_trans rbi)// b_le_sup.
Qed.

Lemma disj_abcd n :
  \bigcup_(i < n.+1) `[c_ n i, d_ n i]%classic `&`
  \bigcup_(i < n) contiguous_itvs Z (h1 i) = set0.
Proof.
rewrite eqEsubset; split => x//=.
move=> [[i/= iltn2 xcidi] [j/= jltn1]].
rewrite contiguous_ooitv//= -/(A j) -/(B j).
have [[idx_ord idx_inv] /= [idx_ordE inv_ord ord_inv]] := OrderedBounds.idx_bij A B n.
rewrite -/OrderedBounds.idx in idx_ordE.
destruct n => //.
set j' : 'I_ n.+1 := Ordinal jltn1.
have -> : j = nat_of_ord j' by [].
rewrite -(ord_inv j').
rewrite (_ : idx_inv j' = Ordinal (ltn_ord (idx_inv j'))).
  exact/val_inj.
rewrite -idx_ordE.
rewrite (OrderedBounds.idxE A B d)//.
have [] := @ListOfBounds.nth_abiE _ A B d n.+1 (idx_inv j'); first by [].
move=> <- <- _.
rewrite -OrderedBounds.anth -OrderedBounds.bnth.
rewrite in_itv/= => /andP[aj'x bxj'].
move : xcidi.
rewrite OrderedBounds.cbE OrderedBounds.daE.
rewrite in_itv/=; apply/negP; rewrite negb_and -!ltNge; apply/orP.
case: i iltn2 => /=.
  move=> _; right.
  apply: le_lt_trans aj'x.
  by rewrite le_sorted_leq_nth// ?ListOfBounds.sorted_seq_a// inE size_tuple.
move=> i.
rewrite ltnS => iltn1.
have [ji|ij] := leqP (idx_inv j') i.
  left.
  rewrite (lt_le_trans bxj')//.
  by rewrite le_sorted_leq_nth ?(OrderedBounds.sorted_seq_b _ _ trivIsetAB)// inE size_tuple.
right.
apply: le_lt_trans aj'x.
move: iltn1.
rewrite leq_eqVlt => /predU1P[|].
  move/eq_add_S => eqin.
  rewrite -!/(a_ _ _) /a_ eqin OrderedBounds.a_default//.
  by rewrite OrderedBounds.a_default// -[ltnLHS]eqin.
rewrite ltnS => iltn.
by rewrite le_sorted_leq_nth// ?ListOfBounds.sorted_seq_a// inE size_tuple.
Qed.

Lemma dltc n i j : (j.-1 < n)%N -> (i < j)%N -> d_ n i < c_ n j.
Proof.
move=> nj ij.
rewrite OrderedBounds.daE OrderedBounds.cbE.
case: ifPn => [/eqP j0|j0]; first by rewrite j0 in ij.
have ni : (i < n)%N.
  rewrite (leq_trans ij)//.
  move: nj.
  by rewrite prednK// lt0n.
apply: (@lt_le_trans _ _ (b_ n i)).
  exact: OrderedBounds.a_lt_b.
apply/sorted_leq_nth => //.
- exact: le_trans.
- by apply: OrderedBounds.sorted_seq_b => //; exact: trivIsetAB.
- by rewrite inE !size_tuple.
- by rewrite inE !size_tuple.
- by rewrite -ltnS prednK// lt0n.
Qed.

Lemma disj_cd n :
  trivIset [set: nat] (fun i1 : nat => `]A i1, B i1[%classic) ->
  trivIset (`I_ n.+1) (fun i => `[c_ n i, d_ n i]%classic).
Proof.
move=> trAB.
apply/trivIsetP => i j /= in1 jn1 ij.
wlog : i j in1 jn1 ij / (i < j)%N.
  move=> wlg.
  move: ij; rewrite neq_lt => /orP[|] ij.
    by rewrite wlg// lt_eqF.
  by rewrite setIC wlg// lt_eqF.
move=> {}ij.
rewrite !OrderedBounds.cbE !OrderedBounds.daE.
case: ifPn => [/eqP ->|i0].
  rewrite ifF.
    by contra: ij => ->.
  rewrite -subset0 => x [/=] /[!in_itv]/= /andP[cx xai] /andP[j1x xaj].
  have : b_ n j.-1 <= a_ n 0.
    by rewrite (le_trans _ xai).
  apply/negP; rewrite -ltNge.
  rewrite (@le_lt_trans _ _ (a_ n j.-1))//.
    apply/sorted_leq_nth => //.
    exact: le_trans.
    exact: ListOfBounds.sorted_seq_a.
    by rewrite inE !size_tuple (@ltn_leq_trans j)// (leq_ltn_trans _ ij).
    by rewrite inE !size_tuple prednK// (leq_ltn_trans _ ij).
  apply: OrderedBounds.a_lt_b => //.
  by rewrite prednK// (leq_ltn_trans _ ij).
rewrite ifF.
  contra: i0 => j0.
  by move: ij; rewrite j0.
rewrite -subset0 => x [/=] /[!in_itv]/= /andP[bi1x xai] /andP[j1x xaj].
have : b_ n j.-1 <= a_ n i by rewrite (le_trans _ xai).
apply/negP; rewrite -ltNge.
rewrite (@lt_le_trans _ _ (b_ n i))//.
  apply: OrderedBounds.a_lt_b => //.
  by rewrite (ltn_leq_trans ij).
apply/sorted_leq_nth => //.
- exact: le_trans.
- exact: OrderedBounds.sorted_seq_b.
- by rewrite inE !size_tuple (ltn_leq_trans ij).
- by rewrite inE !size_tuple prednK// (leq_ltn_trans _ ij).
- by rewrite -ltnS prednK// (leq_ltn_trans _ ij).
Qed.

Lemma citvScd k : compact Z -> Z !=set0 ->
  forall n, (n <= k)%N ->
  exists p, (p < n.+1)%N /\
    `]A k, B k[%classic `<=` `[c_ n p, d_ n p].
Proof.
move=> cZ Z_nonempty n nk.
have [x kx] : contiguous_itvs Z (h1 k) !=set0.
  by have[+ _ _] := @bij _ _ _ _ h1; apply.
have [i in1 cdix/=] := citvScd_tmp cZ Z_nonempty kx nk.
exists i; split => //.
(* lemma *)
move=> z /[dup] ABkz.
rewrite /A /B -contiguous_ooitv// => kz.
have [j jn2 cdjz/=] := citvScd_tmp cZ Z_nonempty kz nk.
rewrite -/(c_ _ _) -/(d_ _ _) in cdjz.
suff -> : i = j :> nat by [].
apply/not_notP => /eqP ij.
have [|zx] := leP x z.
  move=> xz.
  have {}ij : (i < j)%N.
    rewrite ltnNge; apply/negP => ji.
    have djci : d_ n j <= c_ n i.
      rewrite OrderedBounds.cbE OrderedBounds.daE.
      have [i0|i0] := eqVneq i 0.
        subst i.
        rewrite leqn0 in ji.
        by rewrite (eqP ji) eqxx in ij.
          (* rewrite [in leRHS]ifF.
            by apply/negbTE. *)
      rewrite /OrderedBounds.a_ /OrderedBounds.b_ -/seq_b.
      apply: (@le_trans _ _ (b_ n j)).
        exact: OrderedBounds.a_le_b.
      rewrite /OrderedBounds.b_.
      rewrite leq_eqVlt eq_sym (negPf ij) /= in ji.
      apply/sorted_leq_nth => //.
      - exact: le_trans.
      - by rewrite OrderedBounds.sorted_seq_b => //; exact: trivIsetAB.
      - by rewrite inE size_tuple (leq_trans ji)// -ltnS.
      - by rewrite inE size_tuple prednK// ?lt0n// -ltnS.
      - rewrite -subn1 leq_subCr ?lt0n// 1?ltnW//.
        by rewrite subn_eq0 -ltnNge.
    have cidj : c_ n i <= d_ n j.
      move: cdix cdjz; rewrite !in_itv/= => /andP[cix xdi] /andP[cjz zdj].
      by rewrite (le_trans cix)// (le_trans xz)//.
    have /eqP : d_ n j = c_ n i.
      by apply/eqP; rewrite eq_le djci cidj.
    rewrite lt_eqF//.
    apply: dltc => //.
      rewrite -subn1.
      rewrite ltn_psubLR//.
      destruct n => //.
      rewrite ltnS leqn0 in jn2.
      rewrite ltnS in in1.
      rewrite leqn0 in in1.
      by rewrite (eqP in1) (eqP jn2) eqxx in ij.
    by rewrite ltn_neqAle eq_sym ij ji.
  have [l ilj [H1 H2]] : exists2 l, (i <= l < j)%N & (d_ n i <= a_ n l <= b_ n l /\ b_ n l <= c_ n j).
    exists i; first by rewrite leqnn ij.
    split.
      rewrite OrderedBounds.daE lexx/=.
      exact: OrderedBounds.a_le_b => // i0.
    rewrite OrderedBounds.cbE ifF.
      by apply/negbTE; rewrite -lt0n (leq_trans _ ij).
    apply/sorted_leq_nth => //.
    - exact: le_trans.
    - by apply: OrderedBounds.sorted_seq_b => //; exact: trivIsetAB.
    - by rewrite !inE !size_tuple (ltn_leq_trans ij).
    - by rewrite !inE !size_tuple prednK// (leq_ltn_trans _ ij).
    - rewrite -ltnS prednK//.
      by rewrite (leq_ltn_trans _ ij).
  have xzk : `[x, z]%classic `<=` contiguous_itvs Z (h1 k).
    move=> t/= txz.
    have := @is_interval_contiguous_itvs _ Z (h1 k) _ _ kx kz t.
    by rewrite !(itvP txz) => /(_ isT).
  have : `]a_ n l, b_ n l[ `<` contiguous_itvs Z (h1 k).
    apply: (proper_subset_trans _ xzk).
    apply/proper_itvoo_cc.
      rewrite OrderedBounds.a_lt_b//.
      by move/andP : ilj => [_ /ltn_leq_trans]; apply; rewrite -ltnS.
    split.
      rewrite (@le_trans _ _ (d_ n i)); last by move/andP : H1 => [].
        by rewrite (itvP cdix).
      by move/andP : H1 => [].
    rewrite (@le_trans _ _ (c_ n j)); last by move/andP : H1 => [].
      by [].
    by rewrite (itvP cdjz).
  rewrite /a_ OrderedBounds.anth.
  rewrite /b_ OrderedBounds.bnth.
  have ln : (l < n)%N.
    move : ilj => /andP[_ /ltn_leq_trans]; apply.
    by rewrite -ltnS.
  have [-> -> ?] := ListOfBounds.nth_abiE A B d ln.
  rewrite /A /B/=.
  rewrite -contiguous_ooitv//.
  apply: contiguous_itvs_not_nested.
  by have [+ _ _] := @bij _ _ _ _ h1; exact.
have {}ij : (j < i)%N.
  rewrite ltnNge; apply/negP => ji.
  have dicj : d_ n i <= c_ n j.
    rewrite OrderedBounds.cbE OrderedBounds.daE.
    have [j0|j0] := eqVneq j 0.
      subst j.
      rewrite leqn0 in ji.
      by rewrite (eqP ji) eqxx in ij.
    apply: (@le_trans _ _ (a_ n j.-1)); last exact: OrderedBounds.a_le_b.
    rewrite -/a_.
    rewrite leq_eqVlt (negbTE ij)/= in ji.
    apply/sorted_leq_nth => //.
    - exact: le_trans.
    - exact: ListOfBounds.sorted_seq_a.
    - rewrite inE (ltn_leq_trans ji)// size_tuple.
      by rewrite ?lt0n// -ltnS.
    - by rewrite inE -ltnS prednK// ?lt0n// size_tuple.
    by rewrite -ltnS prednK ?lt0n.
  have cjdi : c_ n j <= d_ n i.
    move: cdix cdjz; rewrite !in_itv/= => /andP[cix xdi] /andP[cjz zdj].
    by rewrite (le_trans cjz)// (le_trans (ltW zx)).
  have /eqP : d_ n i = c_ n j.
    by apply/eqP; rewrite eq_le cjdi dicj.
  rewrite lt_eqF//.
  apply: dltc => //.
    rewrite -subn1.
    rewrite ltn_psubLR//.
    destruct n => //.
    rewrite ltnS leqn0 in jn2.
    rewrite ltnS in in1.
    rewrite leqn0 in in1.
    by rewrite (eqP in1) (eqP jn2) eqxx in ij.
  by rewrite ltn_neqAle ij ji.
have [l ilj [H1 H2]] : exists2 l, (j <= l < i)%N & (d_ n j <= a_ n l <= b_ n l /\ b_ n l <= c_ n i).
  exists j; first by rewrite leqnn ij.
  split.
    by rewrite OrderedBounds.daE lexx/= OrderedBounds.a_le_b.
  rewrite OrderedBounds.cbE ifF.
    by apply/negbTE; rewrite -lt0n (leq_trans _ ij).
  apply/sorted_leq_nth => //.
  - exact: le_trans.
  - by apply: OrderedBounds.sorted_seq_b => //; exact: trivIsetAB.
  - by rewrite !inE !size_tuple (ltn_leq_trans ij)// -ltnS.
  - by rewrite !inE !size_tuple prednK// ?(leq_ltn_trans _ ij)// -ltnS.
  - by rewrite -ltnS prednK// (leq_ltn_trans _ ij).
have xzk : `[z, x]%classic `<=` contiguous_itvs Z (h1 k).
  move=> t/= txz.
  have := @is_interval_contiguous_itvs _ Z (h1 k) _ _ kz kx t.
  by rewrite !(itvP txz) => /(_ isT).
have : `]a_ n l, b_ n l[ `<` contiguous_itvs Z (h1 k).
  apply: (proper_subset_trans _ xzk).
  apply/proper_itvoo_cc.
    apply: OrderedBounds.a_lt_b; first by move=> ?; exact: A_lt_B.
    by move/andP : ilj => [_ /ltn_leq_trans]; apply; rewrite -ltnS.
  split.
    rewrite (@le_trans _ _ (d_ n j)); last by move/andP : H1 => [].
      by rewrite (itvP cdjz).
    by move/andP : H1 => [].
  rewrite (@le_trans _ _ (c_ n i)); last by move/andP : H1 => [].
    by [].
  by rewrite (itvP cdix).
rewrite /a_ OrderedBounds.anth.
rewrite /b_ OrderedBounds.bnth.
have ln : (l < n)%N.
  move : ilj => /andP[_ /ltn_leq_trans]; apply.
  by rewrite -ltnS.
have [-> -> ?] := ListOfBounds.nth_abiE A B d ln.
rewrite -contiguous_ooitv//.
apply: contiguous_itvs_not_nested.
by have [+ _ _] := @bij _ _ _ _ h1; exact.
Qed.

(* TODO: weaken hypothesis, without (perfect_set Z)? *)
Lemma cltd n i : Z !=set0 -> perfect_set Z ->
  (i < n.+1)%N -> c_ n i < d_ n i.
Proof.
move=> Z0 /[dup]pZ /perfectP[cZ iZ0] iltn1.
have compactZ : compact Z by rewrite Rcompact_boundE.
have Zc : Z c by rewrite ((closure_id _).1 cZ); exact: closure_inf.
have Zd : Z d by rewrite ((closure_id _).1 cZ); exact: closure_sup.
have citvE p q : (q < p)%N ->
  contiguous_itvs Z (h1 (OrderedBounds.idx A B p q)) = `]a_ p q, b_ p q[%classic.
  rewrite contiguous_ooitv// (OrderedBounds.idxE A B d p q) -/(A _) -/(B _) => pq.
  by have [<- <- _] := ListOfBounds.nth_abiE A B d pq; rewrite -OrderedBounds.anth -OrderedBounds.bnth.
rewrite lt_neqAle c_le_d// andbT.
have inf_lt_sup : c < d.
  apply: has_bound_not_subset1_inf_sup => //; move/is_subset1P => [|[x Z1]].
    exact/eqP/set0P.
  by move: iZ0; rewrite Z1 is_subset1_isolated; apply/eqP/set0P; exists x.
rewrite OrderedBounds.cbE OrderedBounds.daE; case: i iltn1 => //=[|i].
  case: n => //[_|n _].
    by rewrite OrderedBounds.a_default// lt_eqF.
  apply/negP => /eqP inf_eq_a.
  move/eqP : iZ0; apply/negP/set0P; exists c; split; rewrite ?inE//.
  exists `]c - 1, b_ n.+1 0[%classic => //.
    rewrite nbhsE/=; exists `]c - 1, b_ n.+1 0[%classic => //; split => //=.
    by rewrite in_itv/= inf_eq_a OrderedBounds.a_lt_b// gtrBl andbT.
  rewrite eqEsubset; split.
    move=> x/=[+ Zx]; rewrite in_itv/= => /andP[c1x xb0].
    apply/eqP; rewrite eq_le leNgt.
    have/sub_Rhull := Zx; rewrite compact_Rhull//= in_itv/= => /andP[-> _].
    rewrite andbT; apply/negP => cx; move: Zx.
    apply: (@contiguous_itvs_subsetC _ _ (h1 (OrderedBounds.idx A B n.+1 0))).
    by rewrite citvE//= in_itv/= /a_ -inf_eq_a cx xb0.
  by rewrite sub1set inE/= in_itv/= gtrBl /b_ {1}inf_eq_a OrderedBounds.a_lt_b ?andbT.
rewrite ltnS leq_eqVlt => /predU1P[i1n|i1n].
  rewrite i1n OrderedBounds.a_default//.
  apply/negP => /eqP b_eq_sup; move/eqP: iZ0; apply/negP/set0P.
  exists d; split; rewrite ?inE//; exists `]a_ n i, d + 1[%classic => //.
    rewrite nbhsE/=; exists `]a_ n i, d + 1[%classic => //; split => //=.
    by rewrite in_itv/= ltrDl -b_eq_sup OrderedBounds.a_lt_b ?i1n/=.
  rewrite eqEsubset; split.
    move=> x/=[+ Zx]; rewrite in_itv/= => /andP[aix xd1].
    apply/eqP; rewrite eq_le; have/sub_Rhull := Zx; rewrite compact_Rhull//=.
    rewrite in_itv/= (leNgt d) => /andP[_ ->]; apply/negP => xd; have := Zx.
    apply: (@contiguous_itvs_subsetC _ _ (h1 (OrderedBounds.idx A B n i))).
    by rewrite citvE -i1n//= in_itv/= i1n /b_ b_eq_sup aix xd.
  by rewrite sub1set inE/= in_itv/= ltrDl /a_ -{2}b_eq_sup OrderedBounds.a_lt_b ?i1n/=.
apply/negP => /eqP b_eq_a.
move/eqP: iZ0; apply/negP/set0P; exists (a_ n i.+1); split.
  rewrite /a_ OrderedBounds.anth; have [-> _ _] := ListOfBounds.nth_abiE A B d i1n; rewrite inE.
  by apply: mem_contiguous_itvs1; have [+ _ _] := @bij _ _ _ _ h1; exact.
exists `]a_ n i, b_ n i.+1[%classic => //.
  rewrite nbhsE/=; exists `]a_ n i, b_ n i.+1[%classic => //; split => //=.
  by rewrite in_itv/= /a_  -{1}b_eq_a !OrderedBounds.a_lt_b// ltnW.
rewrite eqEsubset; split=> [x [/= + Zx]|].
  rewrite in_itv/= => /andP[aix xbi1].
  apply/eqP; rewrite eq_le -(negbK (_ && _)) negb_and -!ltNge; apply/negP.
  move=> /orP[ai1x|].
    move: Zx; apply: cplt_hull_complement.
    apply: (@contiguous_itvsS _ _ (h1 (OrderedBounds.idx A B n i.+1))).
    by rewrite citvE//= in_itv/= ai1x xbi1.
  rewrite /a_ -b_eq_a => xbi; move: Zx.
  apply: cplt_hull_complement.
  apply: (@contiguous_itvsS _ _ (h1 (OrderedBounds.idx A B n i))).
  by rewrite citvE//= ?in_itv/= ?aix ?xbi// ltnW.
rewrite sub1set inE/= in_itv/= /a_ -b_eq_a OrderedBounds.a_lt_b ?b_eq_a ?OrderedBounds.a_lt_b//= ?(ltnW i1n)//.
split => //; rewrite /a_ OrderedBounds.anth; have [-> _ _] := ListOfBounds.nth_abiE A B d i1n.
by apply: mem_contiguous_itvs1; have [+ _ _] := @bij _ _ _ _ h1; exact.
Qed.

End contiguous_itvs.
End ContItvs.

Module Ene6_direct.
Section ene6_direct.
Context {R : realType} (a b : R) (ab : a < b) (f : R -> R).

Hypotheses (cf : {within `[a, b], continuous f})
           (bvf : bounded_variation a b f)
           (lusinf : lusinN `[a, b] f).
Definition H := fun x => fine (total_variation a ^~ f x).

(* "Clearly, H is increasing and continuous. " *)
Let ndH := bounded_variation_total_nondecreasing bvf.
Let cH : {within `[a, b], continuous H}.
Proof. exact: total_variation_continuous. Qed.

Import MeasurableR.

Local Notation mu := (@lebesgue_measure R).

(* https://math.stackexchange.com/questions/520209/removing-isolated-points-to-get-a-perfect-set *)
Lemma ene6_direct : lusinN `[a, b] H.
Proof.
apply: contrapT => nl.
(* use lemma 3 *)
have [Z [Zab cZ isoZ0 Z0 HZ]] : exists Z : set R,
    [/\ Z `<=` `[a, b], compact Z, isolated Z = set0,
        mu Z = 0 & (0%R < mu [set H x | x in Z])%E].
  (* lemma3 *)
  have := image_measure0_Lusin_nondecreasing_isolated0 ab cH ndH.
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
have perfectZ : perfect_set Z by exact/perfectP.
have Z_nonempty : Z !=set0.
  apply/set0P; apply/negP => /eqP Z0'.
  by move: HZ; rewrite Z0' image_set0 measure0 ltxx.
have closedZ : closed Z by exact: compact_closed cZ.
pose supp := contiguous_itvs_support Z.
have infsupp := contiguous_infinite Zab cZ Z_nonempty Z0 perfectZ.
have countsupp : countable supp by exact: subset_card_le.
have /ppcard_eqP[/= h] := eq_card_nat countsupp infsupp.
pose h1 : {splitbij [set: nat] >-> supp} := h^-1%FUN.
have h1h : {in supp, cancel h h1} by exact: funK.
have hh1 : cancel h1 h by move=> x; apply: invK; rewrite inE.
have ne_cgitvs n : contiguous_itvs Z (h1 n) !=set0.
  have : supp (h1 n).
    have := @bij _ _ _ _ h1.
    by move=> [+ _ _]; exact.
  by rewrite /supp/contiguous_itvs_support/=.
pose A_ n := contiguous_itvs1 Z (h1 n).
pose B_ n := contiguous_itvs2 Z (h1 n).
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
    by rewrite set_itv1 lebesgue_measure_set1.
  rewrite lebesgue_measure_itv ifT ?lte_fin//=.
  by rewrite -EFinB ltry.
pose a_ := OrderedBounds.a_ A_ B_ d.
pose b_ := OrderedBounds.b_ A_ B_ d.
pose idx := OrderedBounds.idx A_ B_.
have lbZa : lbound Z a by move=> r /Zab /itvP ->.
have ubZb : ubound Z b by move=> r /Zab /itvP ->.
pose cd_ := OrderedBounds.cd_ A_ B_ c d.
pose seq_c := OrderedBounds.seq_c A_ B_ c d.
pose seq_d := OrderedBounds.seq_d A_ B_ c d.
pose c_ := OrderedBounds.c_ A_ B_ c d.
pose d_ := OrderedBounds.d_ A_ B_ c d.
(* for non-increasingness of lambda
have cdS_split n j : exists k, [/\ (k < n.+1)%N,
  c_ n.+1 k \in `[B_ (idx n k), (A_ (idx n k.+1))],
  d_ n.+1 k \in `[B_ (idx n k), (A_ (idx n k.+1))] &
  cd_ n.+1 = take k (cd_ n) ++
   [:: (B_ n.+1, A_ n.+1)] ++
   drop k (cd_ n)].
  admit.
*)
pose lambda n := diam_max [seq `[c_ n i, d_ n i]%classic | i <- iota 0 n.+1].
have lambda_fin n : lambda n \is a fin_num.
  rewrite ge0_fin_numE; first exact: diam_max_ge0.
  rewrite /lambda /diam_max big_seq_cond; apply: bigmax_lt; first by [].
  move=> s; rewrite andbT.
  move/mapP => [i].
  rewrite mem_iota add0n => /andP[_ iltn2 ->].
  by rewrite diam_itv ?ltry ?ContItvs.c_le_d.
have lambda_ge0 n : (0 <= lambda n)%E by exact: diam_max_ge0.
have mcgitv i : mu.-cara.-measurable (contiguous_itvs Z i).
  apply: open_measurable.
  exact: open_contiguous_itvs.
have lambda0 : (fine \o lambda) @ \oo --> 0%R.
  apply: fine_cvg.
  apply (@squeeze_cvge _ _ _ R (cst 0) _
    (fun n => \sum_(i < n.+1) mu `[c_ n i, d_ n i])) => //.
  - near=> n; apply/andP; split; first exact: lambda_ge0.
      rewrite /lambda /diam_max big_tuple.
      apply: bigmax_le.
      exact: leNye.
    move=> /= i _.
    rewrite tnth_map (tnth_nth 0) nth_iota// add0n.
    rewrite diam_itv; first exact: ContItvs.c_le_d.
    rewrite (bigD1 i)//=.
    have -> : mu `[c_ n i, d_ n i] = (d_ n i - c_ n i)%:E.
      rewrite lebesgue_measure_itv lte_fin.
      have [_|] := ltP (c_ n i) (d_ n i).
        by rewrite /= -EFinB.
      rewrite le_eqVlt; move/predU1P => [->|].
        by rewrite subrr.
      by rewrite ltNge ContItvs.c_le_d.
    by rewrite leeDl// sume_ge0.
  - apply: (@cvg_trans _
      (mu (\bigcap_(i < n) ([set` Rhull Z] `\` (contiguous_itvs Z (h1 i))))
        @[n --> \oo])).
    apply: near_eq_cvg.
    near=> n.
    have n0 : (0 < n)%N by near: n; exact: nbhs_infty_gt.
    destruct n => //.
    transitivity (mu (\bigcup_(i < n.+2) `[c_ n.+1 i, d_ n.+1 i]%classic)).
      congr mu.
      rewrite -setD_bigcupr; first by exists 0.
      rewrite (ContItvs.hullZ_abcd lbZ ubZ h1 n.+1 cd cZ Z_nonempty)//.
      rewrite setDUD.
      have -> : \bigcup_(i < n.+1) `]a_ n.+1 i, b_ n.+1 i[%classic
        `\` \bigcup_(i < n.+1) contiguous_itvs Z (h1 i) = set0.
        rewrite eqEsubset; split => // x/=.
        apply/not_implyP; apply.
        move=> [i/= iltn1].
        rewrite /a_ OrderedBounds.anth /b_ OrderedBounds.bnth.
        have [-> -> idxltn1] := ListOfBounds.nth_abiE A_ B_ d iltn1.
        rewrite -!OrderedBounds.idxE => xAB.
        exists (idx n.+1 i) => //=.
          rewrite /idx (OrderedBounds.idxE A_ B_ d).
          by rewrite (leq_trans idxltn1)//.
        by rewrite contiguous_ooitv.
      rewrite setU0.
      apply: setDidl.
      exact: ContItvs.disj_abcd.
    rewrite bigcup_mkord.
    rewrite measure_semi_additive_ord//=.
      (* lemma? *)
      case => i iltn2.
      case => j jltn2 _ _/=.
      move=> [x/= [xi xj]]/=.
      rewrite -(inord_val (Ordinal _))/=.
      rewrite -(inord_val (Ordinal _))/=.
      apply: ord_inj; rewrite !inordK//.
      apply/eqP/not_notP => /negP => ij.
      wlog : i j iltn2 jltn2 x xi xj ij / (i < j)%N.
        move=> H.
        move: (ij); rewrite neq_ltn => /orP[iltj|jlti].
          exact: (H i j _ _ x).
        apply: (H j i _ _ x) => //.
        by rewrite eq_sym.
      move=> {}ij.
      move: xi xj.
      rewrite !in_itv/= => /andP[_ +] /andP[+ _].
      move/[swap]/le_trans => H /H {H}.
      apply/negP; rewrite -ltNge.
      rewrite /d_ OrderedBounds.daE /c_ OrderedBounds.cbE.
      case: j jltn2 ij => //=j.
      rewrite !ltnS => jn ij.
      apply: (@le_lt_trans _ _ (a_ n.+1 j)).
        rewrite le_sorted_leq_nth// ?ListOfBounds.sorted_seq_a// inE size_tuple//.
        by rewrite (leq_ltn_trans ij).
      rewrite /a_ OrderedBounds.anth /b_ OrderedBounds.bnth.
      have : (j < n.+1)%N by rewrite ltnS.
      move=> /(@ListOfBounds.nth_abiE R A_ B_ d n.+1 j)[-> -> _].
      exact: contiguous_itvs1_lt_contiguous_itvs2.
    exact: bigsetU_measurable.
  have <- : mu (\bigcap_n ([set` Rhull Z] `\` (contiguous_itvs Z (h1 n)))) = 0%:E.
    rewrite -setD_bigcupr//.
    have [funh1 injh1 surjh1] := @bij _ _ _ _ h1.
    rewrite -(reindex_bigcup _ _ _ _ funh1 surjh1).
    rewrite -bigcup_contiguous_itvs_support.
    rewrite -cplt_hull_contiguous_itvs//.
    rewrite setDD setIidr; first exact: sub_Rhull.
    exact: Z0.
  apply: cvg_measure_bigcap => /=.
    by move=> ?; apply: measurableD => //; exact: sub_caratheodory.
  apply: (@le_lt_trans _ _ (mu [set` Rhull Z])).
    apply: le_outer_measure.
    exact: subDsetl.
  rewrite compact_Rhull//.
  rewrite lebesgue_measure_itv//= lte_fin.
  rewrite cd.
  by rewrite -EFinB ltry.
(* pose CD_ n := merge <=%R [tuple c_ n i | i < n.+1] [tuple d_ n i | i < n.+1]. *)
(* xs := flatten
 * [:: [:: d_ n 0 + 1 * (c_ n 1 - d_ n 0) / k_ i, c + 2 * (c_ n 1 - d_ n 0) / k_ i, ... , c_ n 1],
 *    [:: d_ n 1],
 *    [:: d_ n 1 + 1 * (c_ n 2 - d_ n 1) / k_ i, ... , c_ n 2],
 *    [:: d_ n 2],
 *    ...
 *    [:: d_ n n]]
 *  [remark]: c_ n 0 = c, d_ n n = d, k_ i = number of points between (d_ n i) and (c_ n i.+1)
 *)
have lambda_gt0 n : 0 < fine (lambda n).
  have cdab i : (i < n.+1)%N -> `[c_ n i, d_ n i]%classic `<=` `[a, b]%classic.
    move=> in1.
    apply: (@subset_trans _ [set` Rhull Z]).
      by rewrite (ContItvs.hullZ_abcd _ _ h1 n)//; move=> x xcdi; left; exists i.
    rewrite -(@RhullK _ `[a, b]%classic).
      by rewrite inE; exact: interval_is_interval.
    exact: le_Rhull.
  (* because HZ : 0 < mu (H @` Z), there exists i s.t. c_ n i < d_ n i*)
  rewrite ltNge; apply/negP.
  rewrite le_eqVlt; move/orP; case; last first.
    by apply/negP; rewrite -leNgt -lee_fin fineK.
  move=> /eqP lambda_eq0.
  move: HZ.
  apply/negP.
  rewrite -leNgt.
  suff : (mu (\bigcup_(i < n.+1) H @` `[c_ n i, d_ n i]%classic) <= 0)%E.
    apply: le_trans.
    apply: le_outer_measure.
    rewrite -image_bigcup.
    apply: image_subset.
    exact: ContItvs.Zcd.
  rewrite bigcup_mkord.
  apply: (@le_trans _ _
      (\sum_(i < n.+1) mu [set H x | x in `[c_ n i, d_ n i]])).
    exact: (outer_measure_subadditive mu
         (fun i => [set H x | x in `[c_ n i, d_ n i]])).
  apply: sume_le0 => i _.
  apply: (@le_trans _ _ (mu `[H (c_ n i), H (d_ n i)])).
    apply: le_outer_measure.
    apply: continuous_nondecreasing_image_itvcc.
    - exact: ContItvs.c_le_d.
    - apply: continuous_subspaceW cH.
      exact: cdab.
    apply: itv_sub_in2 ndH.
    exact: cdab.
  rewrite lebesgue_measure_itv/= ifF//.
  apply/negP/negP; rewrite -leNgt le_eqVlt; apply/predU1P; left.
  congr (H _)%:E.
  apply/eqP; rewrite eq_le; apply/andP; split; last by exact: ContItvs.c_le_d.
  rewrite leNgt; apply/negP => c_lt_d.
  move/eqP: lambda_eq0.
  apply/negP; apply: lt0r_neq0.
  (* because of c_ n i < d_ n i, then 0 < lambda n. *)
  rewrite fine_gt0//; apply/andP; split; last by rewrite -ge0_fin_numE.
  rewrite /lambda/diam_max.
  have memi : `[c_ n i, d_ n i]%classic \in [seq `[c_ n i0, d_ n i0]%classic | i0 <- iota 0 n.+1].
    rewrite (map_f (fun k => `[c_ n k, d_ n k]%classic))//.
    by rewrite mem_iota leq0n add0n/=.
  have := le_bigmax_seq -oo%E _ xpredT (fun X => diam X) memi isT.
  apply: lt_le_trans.
  rewrite diam_itv// ?ContItvs.c_le_d//.
  by rewrite EFinB sube_gt0 lte_fin.
pose unif_part n i : _.-tuple _ :=
  locked uniform_partition (d_ n i) (c_ n i.+1) (fine (lambda n)).
pose xs' n := interleave [seq (unif_part n i : seq _) | i <- iota 0 n]
                         (reshape (nseq n 1) (behead (seq_d n))).
pose xs n := d_ n 0 :: flatten (xs' n).
have pcdxs n : itv_partition c d (xs n).
  case: n.
    rewrite /xs.
    rewrite (_ : flatten _ = [::])//.
    rewrite /itv_partition; split.
      rewrite /= andbT.
      by apply: (le_lt_trans (ContItvs.inf_le_c _ _ _ _ _ _ )) => //; exact: ContItvs.cltd.
    by rewrite /d_ OrderedBounds.daE OrderedBounds.a_default.
  split.
    apply/(pathP d); case.
      move=> _.
      rewrite (_ : c = c_ n.+1 0).
        by rewrite /c_ OrderedBounds.cbE.
      exact: ContItvs.cltd.
    move=> i.
    rewrite ltnS -/(size _).
    rewrite nth_cons.
    rewrite (ltn0Sn i) succnK.
    case: i.
      move=> xs'n10.
      rewrite nth_cons.
      rewrite ltnn.
      rewrite nth_cons (ltn0Sn 0) succnK.
      rewrite nth0_flatten_interleave.
      - by rewrite -size_eq0 size_tuple.
      - by rewrite size_map size_iota size_reshape size_nseq.
      rewrite /unif_part -lock.
      rewrite nth_map_tuple//.
      rewrite ltrDl.
      rewrite mulr_gt0//.
      by rewrite mulr1 subr_gt0 ContItvs.dltc.
    apply/sortedP.
    apply: (@lt_sorted_flatten _ _ d) => //.
    - rewrite (eq_all_r (mem_interleave _))//.
        by rewrite size_map size_iota size_reshape size_nseq.
      rewrite all_cat; apply/andP; split.
        apply/allP => _ /mapP[i + ->].
        rewrite mem_iota => /andP[]; rewrite add0n => _ iltn1.
        by rewrite -size_eq0 gt_eqF// size_tuple.
      rewrite reshape_nseq1 ?size_behead ?size_tuple//.
      by apply/allP => _ /mapP[i + ->].
    - rewrite (eq_all_r (mem_interleave _))//.
        by rewrite size_map size_iota size_reshape size_nseq.
      rewrite all_cat; apply/andP; split.
        apply/allP => _ /mapP[i + ->].
        rewrite mem_iota => /andP[]; rewrite add0n => _ iltn1.
        rewrite /unif_part -lock.
        apply: sorted_uniform_partition => //.
        exact: ContItvs.dltc.
      rewrite reshape_nseq1 ?size_behead ?size_tuple//.
      by apply/allP => _ /mapP[i + ->].
    apply/(sortedP [::]) => i i1xs'.
    rewrite !nth_interleaveE.
    rewrite i1xs' (ltnW i1xs').
    move: i1xs'.
    rewrite size_interleave size_map size_iota size_reshape size_nseq minnn doubleS ltnS => in21.
    rewrite reshape_nseq1 ?size_behead ?size_tuple//.
    case: ifP => [oddi|eveni].
      rewrite ifF.
        by rewrite oddS oddi.
      rewrite (nth_map d)//.
        rewrite size_behead size_tuple/=.
        apply: ltn_div2; rewrite doubleS.
        exact: (ltn_trans in21).
      rewrite nth_behead.
      rewrite nth_map_iota.
        by rewrite ltn_div2.
      rewrite (_ : nth d (seq_d n.+1) i./2.+1 = d_ n.+1 i./2.+1)//.
      rewrite (_ : i.+1./2 = i./2.+1).
        by rewrite -uphalfE uphalf_half oddi add1n.
      rewrite [ltLHS]/=.

      case: n in21.
        rewrite double0 ltnS leqn0 => /eqP i0.
        by move: oddi; rewrite i0.
      move=> n in23.
      have[n2i|] := leqP n.+1.*2.-1 i.
        have : i = n.+1.*2.-1.
          apply/eqP; rewrite eqn_leq n2i andbT.
          move: in23.
          rewrite -odd_uphalfK//.
          rewrite uphalfE halfK/= oddi subn0 ltnS.
          rewrite doubleS.
          rewrite leq_eqVlt => /predU1P[in22|//].
          move: oddi; rewrite in22.
          by rewrite !oddS negbK odd_double.
        move=> ->.
        rewrite [unif_part]lock/= uphalf_double -lock.
        rewrite /unif_part -lock.
        apply: head_uniform_partition => //.
        by rewrite ContItvs.dltc.
      move=> i2n.
      have ? : (i./2.+2.-1 < n.+2)%N.
        rewrite succnK ltnS ltn_half_double.
        exact: (ltn_trans i2n).
      apply: (@lb_uniform_partition _ _ (c_ n.+2 i./2.+2) (fine (lambda n.+2))).
      - exact: ContItvs.dltc.
      - by rewrite lambda_gt0.
      rewrite -nth0.
      rewrite /unif_part -lock.
      apply: mem_nth.
      rewrite size_uniform_partition_gt0//.
      exact: ContItvs.dltc.
    rewrite ifT.
      by rewrite /= eveni.
    rewrite nth_map_iota.
      rewrite -ltn_double even_halfK ?eveni// doubleS.
      exact: (ltn_trans in21).
    rewrite (nth_map d).
      rewrite size_behead size_tuple.
      rewrite -ltn_double odd_halfK ?oddS ?eveni//.
      by rewrite !succnK doubleS (ltn_trans in21).
    rewrite nth_behead.
    rewrite /unif_part -lock.
    rewrite last_uniform_partition.
      apply: ContItvs.dltc => //.
        rewrite succnK -ltn_double even_halfK ?eveni// doubleS.
        exact: (ltn_trans in21).
      exact: lambda_gt0.
    rewrite /= uphalf_half eveni add0n ContItvs.cltd//.
    rewrite ltnS -ltn_double even_halfK ?eveni// doubleS.
    exact: (ltn_trans in21).
  rewrite /xs last_cons last_flatten_interleave//.
  - apply/allP => _ /mapP[i + ->].
    rewrite mem_iota => /andP[]; rewrite add0n => _ iltn1.
    by rewrite -size_eq0 gt_eqF// size_tuple.
  - rewrite reshape_nseq1 ?size_behead ?size_tuple//.
    by apply/allP => _ /mapP[i _ ->].
  - by rewrite size_reshape size_map size_iota size_nseq.
  rewrite reshape_nseq1 ?size_behead ?size_tuple//.
  rewrite (@set_last_default _ [seq _ | _ <- _] [:: d]).
    by rewrite size_map size_behead size_tuple.
  rewrite last_map/=.
  rewrite -nth_last nth_behead prednK.
    by rewrite size_behead size_tuple.
  rewrite size_behead size_tuple/=.
  rewrite (_ : nth d (seq_d n.+1) n.+1 = d_ n.+1 n.+1)//.
  rewrite /d_ OrderedBounds.daE.
  by rewrite OrderedBounds.a_default.
have eq_size_lp_nseq n : size [seq (uniform_partition (d_ n i) (c_ n i.+1)
             (fine (lambda n)) : seq _) | i <- iota 0 n] =
       size (reshape (nseq (size (behead (seq_d n))) 1%N) (behead (seq_d n))).
  by rewrite size_map size_iota size_reshape size_nseq size_behead size_tuple.
have allNnil_xs n : all (fun s : seq R => s != [::]) (xs' n).
  rewrite (eq_all_r (mem_interleave _))//.
    by rewrite size_map size_iota size_reshape size_nseq.
  rewrite all_cat; apply/andP; split.
    apply/all_nthP => i.
    rewrite size_map size_iota => iltn1.
    rewrite nth_map_iota//.
    by rewrite -size_eq0 gt_eqF// size_tuple.
  rewrite reshape_nseq1 ?size_behead ?size_tuple//.
  apply/all_nthP => i.
  rewrite size_map => iltd.
  by rewrite (nth_map d).
have allcd_xs n : all (fun x : R => c <= x <= d) (xs n).
  apply/allP => x.
  rewrite /xs in_cons => /predU1P[->|].
    by rewrite ContItvs.inf_le_d//= ContItvs.d_le_sup.
  move/flattenP => /=[s].
  rewrite mem_interleave//.
    by rewrite size_map size_iota size_reshape size_nseq.
  rewrite mem_cat => /orP[|].
    move/mapP => [i + ->]; rewrite mem_iota add0n => /andP[_ iltn1].
    move=> xlp.
    apply/andP; split.
      rewrite (@le_trans _ _ (d_ n i)) ?ContItvs.inf_le_d//.
      move: xlp.
      rewrite /unif_part -lock.
      move/(@lb_uniform_partition _ (d_ n i) (c_ n i.+1))/ltW; apply.
        rewrite /c_ /d_ OrderedBounds.cbE OrderedBounds.daE/=.
        apply: OrderedBounds.a_lt_b => // j.
        exact: contiguous_itvs1_lt_contiguous_itvs2.
      exact: lambda_gt0.
    rewrite (@le_trans _ _ (c_ n i.+1))//; last exact: ContItvs.c_le_sup.
    move/(nthP d) : xlp => [j Hj <-{x}].
    apply: (@itv_partition_le_ub _ _ _ (d_ n i)) => //.
    rewrite /unif_part -lock.
    apply: itv_uniform_partition => //.
    exact: ContItvs.dltc.
  rewrite reshape_nseq1 ?size_behead ?size_tuple// => /mapP[r rdn] ->.
  rewrite mem_seq1 => /eqP ->{x}.
  move/mem_behead : rdn.
  move/(nthP d) => -[i id <-{r}].
  rewrite (_ : nth _ _ _ = OrderedBounds.d_ A_ B_ c d n i)//.
  by rewrite ContItvs.inf_le_d//= ContItvs.d_le_sup.
have mesh_xs n : mesh c (xs n) <= fine (lambda n).
  rewrite /xs mesh_cons.
  rewrite (_ : c = c_ n 0); first by rewrite /c_ OrderedBounds.cbE eqxx.
  rewrite /maxr; case : ifP => _; last first.
    rewrite /lambda -lee_fin fineK.
      rewrite diam_defaultE//.
      rewrite -(big_map_id _ _ diam _ xpredT).
      rewrite bigmaxe_fin_num// => x /mapP[i /mapP[j]].
      rewrite mem_iota leq0n add0n/= => jn ->{i} ->{x}.
      rewrite diam_ge0; split => //.
      by rewrite diam_itv//= ContItvs.c_le_d.
    rewrite (le_trans _ (diam_max_cons _ _))//.
    rewrite diam_itv; first exact: ContItvs.c_le_d.
    by rewrite ger0_norm// subr_ge0 ContItvs.c_le_d.
  rewrite (@mesh_flatten _ _ d)//.
  - apply/allP => /= i /flattenP[j ].
    rewrite /xs'.
    rewrite mem_interleave.
      by rewrite size_map size_iota size_reshape size_nseq.
    rewrite mem_cat => /orP[/mapP[k]|].
      rewrite mem_iota add0n leq0n => kn ->.
      move=> /(nthP d)[l lsz] <-{i}.
      apply/andP; split.
        rewrite (@le_trans _ _ (d_ n k))//.
          rewrite /d_ !OrderedBounds.daE -/(a_ _).
          apply/le_sorted_leq_nth => //; [|by rewrite inE/= size_tuple (leq_trans _ kn)..].
          exact: ListOfBounds.sorted_seq_a.
        rewrite -[leRHS]/(nth d (d_ n k :: unif_part n k) l.+1).
        apply: itv_partition_nth_ge_with_def => //.
        rewrite /unif_part -lock.
        apply: itv_uniform_partition => //.
        by rewrite ContItvs.dltc.
      rewrite (@le_trans _ _ (c_ n k.+1))//.
        apply/(@itv_partition_le_ub _ _ _ (d_ n k)) => //.
        rewrite /unif_part -lock.
        apply: itv_uniform_partition => //.
        exact: ContItvs.dltc.
      exact: ContItvs.c_le_sup.
    rewrite reshape_nseq1 ?size_behead ?size_tuple// => /mapP[k].
    move=> /(nthP d)[l].
    rewrite size_behead size_tuple => /= ln <-{k} ->{j}.
    rewrite mem_seq1 => /eqP ->{i}.
    rewrite -[X in _ <= X <= _]/(nth d [tuple of (thead (seq_d n) :: behead (seq_d n))] l.+1).
    rewrite -tuple_eta.
    apply/andP; split.
      apply/le_sorted_leq_nth => //=; [|by rewrite inE size_tuple..].
      exact: ContItvs.sorted_d.
    rewrite -[leLHS]/(d_ _ _).
    by rewrite /d_ OrderedBounds.daE ContItvs.a_le_sup.
  - apply/(@le_sorted_flatten _ _ d).
    + (* all (fun s : seq R => s != [::]) (xs' n) *)
      apply/allP => z.
      rewrite /xs' reshape_nseq1 ?size_behead ?size_tuple// mem_interleave.
        by rewrite !size_map size_behead size_iota size_tuple.
      rewrite mem_cat => /orP[|].
        move=> /mapP[/= i]; rewrite mem_iota leq0n add0n/= => ni ->{z}.
        rewrite -size_eq0 -lt0n.
        rewrite /unif_part -lock.
        by rewrite size_uniform_partition_gt0// ContItvs.dltc.
      by move=> /mapP[/= i] _ ->.
    + (* all (sorted <=%R) (xs' n) *)
      apply/allP => z.
      rewrite /xs'.
      rewrite /xs' reshape_nseq1 ?size_behead ?size_tuple// mem_interleave.
        by rewrite !size_map size_behead size_iota size_tuple.
      rewrite mem_cat => /orP[|].
        move=> /mapP[/= i]; rewrite mem_iota leq0n add0n/= => ni ->{z}.
        have : d_ n i < c_ n i.+1 by rewrite ContItvs.dltc.
        move/itv_uniform_partition => /(_ _ (lambda_gt0 n))[+ _].
        rewrite /unif_part -lock.
        by move/path_ltW/path_sorted.
      by move=> /mapP[i] ? ->.
    + (* sorted (fun s t : seq R => last d s <= head d t) (xs' n) *)
      apply/(sortedP [::]) => i.
      rewrite size_interleave size_map size_iota size_reshape size_nseq minnn => ni.
      rewrite !nth_interleaveE size_interleave.
      rewrite size_map size_iota size_reshape size_nseq minnn.
      rewrite reshape_nseq1 ?size_behead ?size_tuple//.
      rewrite ni (ltnW ni) oddS.
      case: ifPn => oddi/=.
        rewrite (nth_map d).
          rewrite size_behead size_tuple/=.
          by rewrite ltn_half_double (leq_trans _ ni).
        rewrite nth_map_iota.
          by rewrite ltn_uphalf_double.
        rewrite [leLHS]/=.
        rewrite -[leLHS]/(nth d [tuple of (thead (seq_d n) :: behead (seq_d n))] i./2.+1).
        rewrite -tuple_eta -[leLHS]/(d_ n i./2.+1).
        have := uphalf_half i.
        rewrite oddi add1n => <-.
        apply/ltW.
        have : d_ n (uphalf i) < c_ n (uphalf i).+1.
          apply/ContItvs.dltc => //.
          by rewrite ltn_uphalf_double.
        move/lb_uniform_partition => /(_ _ (lambda_gt0 n)); apply.
        rewrite -nth0.
        rewrite /unif_part -lock.
        apply/mem_nth.
        apply: size_uniform_partition_gt0 => //.
        rewrite ContItvs.dltc//.
        by rewrite ltn_uphalf_double.
      rewrite (nth_map d).
        by rewrite size_behead size_tuple/= ltn_uphalf_double.
      rewrite nth_map_iota.
        by rewrite ltn_half_double (ltnW ni).
      rewrite [leRHS]/=.
      rewrite -[leRHS]/(nth d [tuple of (thead (seq_d n) :: behead (seq_d n))] (uphalf i).+1).
      rewrite -tuple_eta -[leRHS]/(d_ n (uphalf i).+1).
      rewrite /unif_part -lock.
      rewrite last_uniform_partition//.
      rewrite ContItvs.dltc//.
        by rewrite ltn_half_double (ltnW ni).
      rewrite uphalf_half (negPf oddi).
      by rewrite ContItvs.c_le_d.
  rewrite size_interleave size_map size_iota.
  rewrite size_reshape size_nseq minnn.
  apply: bigmax_le.
    by rewrite -lee_fin fineK.
  case; case.
    move=> n0 _.
    rewrite (_ : nat_of_ord (Ordinal n0) = 0)//.
    rewrite (_ : nth d [seq last d s | s <- [:: d_ n 0] :: xs' n] 0 = d_ n 0)//.
    have ? : (0 < size (xs' n))%N.
      by rewrite size_interleave size_map size_iota size_reshape size_nseq minnn.
    rewrite nth_interleaveE.
    rewrite ifT//.
    rewrite nth_map_iota.
      by rewrite ltn_half_double.
    apply: ltW.
    rewrite /unif_part -lock.
    apply: uniform_partition_mesh => //.
    by apply: ContItvs.dltc => //=; rewrite -double_gt0.
  move=> i i1ltn2 _.
  rewrite (_ : nat_of_ord (Ordinal i1ltn2) = i.+1)//.
  rewrite (_ : (nth d [seq last d s | s <- [:: _] :: xs' n] i.+1) =
                 (nth d [seq last d s | s <- xs' n] i))//.
  rewrite nth_interleaveE.
  rewrite size_interleave size_map size_iota size_reshape size_nseq minnn.
  rewrite i1ltn2.
  have size_xs' m : size (xs' m) = m.*2.
    rewrite size_interleave size_map size_iota reshape_nseq1.
      by rewrite size_behead size_tuple.
    by rewrite size_map size_behead size_tuple minnn.
  case: ifPn => [eveni|oddi].
    rewrite (nth_map [::])//.
      by rewrite size_xs' ltnW.
    rewrite [X in nseq X](_ : _ = size (behead (seq_d n))).
      by rewrite size_behead size_tuple.
    rewrite reshape_nseq1//.
    rewrite (nth_map d).
      rewrite size_behead size_tuple.
      by rewrite ltn_half_double.
    rewrite mesh_seq1.
    rewrite nth_interleaveE size_xs' (ltnW i1ltn2).
    rewrite oddS in eveni.
    rewrite (negPf eveni).
    rewrite nth_map_iota.
      by rewrite ltn_half_double ltnW.
    rewrite /unif_part -lock.
    rewrite last_uniform_partition.
      by rewrite ContItvs.dltc// ltn_half_double ltnW.
      by rewrite lambda_gt0.
    rewrite -[nth _ _ _]/(nth d [tuple of (thead (seq_d n) :: behead (seq_d n))] i.+1./2.+1).
    rewrite -tuple_eta.
    rewrite -[nth _ _ _]/(d_ n (uphalf i).+1).
    rewrite uphalf_half (negPf eveni) add0n.
    rewrite -lee_fin fineK.
      exact: lambda_fin.
    rewrite /lambda distrC.
    rewrite diam_defaultE//.
    rewrite ler0_norm.
      by rewrite subr_le0 ContItvs.c_le_d.
    rewrite opprB.
    rewrite -(diam_itv true false).
      by rewrite ContItvs.c_le_d.
    apply: le_bigmax_seq => //.
    apply/mapP; exists i./2.+1 => //.
    by rewrite mem_iota add0n leq0n/= ltnS ltn_half_double ltnW.
  rewrite (nth_map [::])//.
    by rewrite size_xs' ltnW.
  rewrite nth_map_iota.
    by rewrite ltn_half_double.
  rewrite nth_interleaveE size_xs' (ltnW i1ltn2).
  rewrite oddS negbK in oddi.
  rewrite oddi.
  rewrite reshape_nseq1 ?size_behead ?size_tuple//.
  rewrite (nth_map d).
    by rewrite size_behead size_tuple ltn_half_double ltnW.
  rewrite /=.
  rewrite -[nth _ _ _]/(nth d [tuple of (thead (seq_d n) :: behead (seq_d n))] i./2.+1).
  rewrite -tuple_eta.
  rewrite -[nth _ _ _]/(d_ n (i./2).+1).
  rewrite uphalf_half oddi add1n.
  (* *)
  rewrite ltW//.
  rewrite /unif_part -lock.
  rewrite uniform_partition_mesh.
  rewrite ContItvs.dltc//=.
  rewrite -ltn_half_double in i1ltn2.
  rewrite (leq_trans _ i1ltn2)//.
  rewrite ltnS.
  rewrite ltn_half_double.
  have := odd_double_half i.+1.
  by rewrite oddS oddi add0n => ->.
  exact: lambda_gt0.
  done.
pose S_ n : R := variation c d f (xs n).
(* (2) *)
pose V_ n : \bar R := \sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)|%:E +
     (\sum_(i < n) total_variation (a_ n i) (b_ n i) f).
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
have cdcf : {within `[c, d], continuous f}.
  apply: continuous_subspaceW cf.
  by apply: subset_itv; rewrite bnd_simp.
have SV n : ((S_ n)%:E <= V_ n)%E.
  rewrite /S_ /V_.
  rewrite /xs.
  rewrite variation_recl big_ord_recl EFinD -addeA.
  apply: leeD.
    by rewrite /= /c_ OrderedBounds.cbE/=.
  rewrite variation_flatten_interleave_split//.
    rewrite all_cat; apply/andP; split => //.
      apply/(all_nthP [::]) => i.
      rewrite size_map size_iota => ni.
      rewrite nth_map_iota//.
      by rewrite -size_eq0 gt_eqF// size_tuple.
    rewrite reshape_nseq1 ?size_behead ?size_tuple//.
    apply/all_nthP => i.
    rewrite size_map size_behead size_tuple/= => iltn.
    by rewrite (nth_map d)// size_behead size_tuple.
  rewrite size_map size_iota.
  rewrite reshape_nseq1 ?size_behead ?size_tuple// minnn.
  rewrite EFinD addrC leeD//.
    rewrite -sumEFin; apply: lee_sum => /= i _.
    rewrite (_ : nth d [seq last d s | s <- [seq (unif_part n i0 : seq _) | i0 <- iota 0 n]] i =
                 b_ n i).
    rewrite (nth_map [::]).
      by rewrite size_map size_iota.
    rewrite nth_map_iota => //.
      rewrite /unif_part -lock last_uniform_partition//.
        by rewrite ContItvs.dltc/=.
      by rewrite /c_ OrderedBounds.cbE.
    rewrite (_ : (nth d [seq last d s | s <- [seq [:: x] |
                                  x <- behead (seq_d n)]] i) = a_ n i.+1).
      rewrite (nth_map [::]).
        by rewrite size_map size_behead size_tuple.
      rewrite (nth_map d)/=.
        by rewrite size_behead size_tuple.
      rewrite nth_behead.
      rewrite /seq_d.
      by rewrite -/(OrderedBounds.d_ _ _ _ _ n i.+1) OrderedBounds.daE.
    rewrite (nth_map d).
      by rewrite size_behead size_tuple.
    rewrite /bump/= add1n.
    rewrite /c_ /d_ OrderedBounds.cbE OrderedBounds.daE/=.
    rewrite /variation/=.
    rewrite big_nat1//=.
    rewrite nth_behead.
    by rewrite /seq_d -/(OrderedBounds.d_ _ _ _ _ n i.+1) OrderedBounds.daE.
  rewrite -sumEFin; apply: lee_sum => /= i _.
  rewrite (_ : nth d [seq last d s | s <- [seq (unif_part n i0 : seq _) | i0 <- iota 0 n]] i =
               b_ n i).
    rewrite (nth_map [::]).
      by rewrite !size_map size_iota.
    rewrite nth_map_iota//.
    rewrite /unif_part -lock.
    rewrite last_uniform_partition//.
      by rewrite ContItvs.dltc/=.
    by rewrite /c_ OrderedBounds.cbE.
  case: i; case => //.
    rewrite /= => n0.
    rewrite nth_map_iota//.
    rewrite /unif_part -lock.
    rewrite /c_ /d_ OrderedBounds.cbE OrderedBounds.daE/=.
    have A_lt_B k : A_ k < B_ k by exact: contiguous_itvs1_lt_contiguous_itvs2.
    have [] := itv_uniform_partition (OrderedBounds.a_lt_b d A_lt_B n0) (lambda_gt0 n).
    move=> /path_ltW pl llb.
    apply: variation_le_total_variation => //.
    by rewrite (eqP llb).
  move=> i/= i1ltn.
  rewrite (_ : (nth d [seq last d s | s <- [seq [:: x] |
                              x <- behead (seq_d n)]] i) = a_ n i.+1).
    rewrite (nth_map [::]).
      by rewrite size_map size_behead size_tuple ltnW.
    rewrite (nth_map d)/=.
      by rewrite size_behead size_tuple ltnW.
    rewrite nth_behead/=.
    by rewrite /seq_d -/(OrderedBounds.d_ _ _ _ _ n i.+1) OrderedBounds.daE.
  have A_lt_B k : A_ k < B_ k.
    exact: contiguous_itvs1_lt_contiguous_itvs2.
  have[] := (itv_uniform_partition (OrderedBounds.a_lt_b d A_lt_B i1ltn) (lambda_gt0 n)).
  move=> /path_ltW pl llb.
  apply: variation_le_total_variation.
    rewrite nth_map_iota//.
    rewrite /unif_part -lock.
    by rewrite /c_ /d_ OrderedBounds.cbE OrderedBounds.daE.
  rewrite nth_map_iota//.
  rewrite /unif_part -lock.
  rewrite /c_ /d_ OrderedBounds.cbE OrderedBounds.daE//.
  by rewrite (eqP llb).
set Vcd : \bar R := total_variation c d f.

pose c' n := [tuple c_ n i | i < n.+1].
pose d' n := [tuple d_ n i | i < n.+1].
have : forall n, exists u v, c' n = u :: v :> seq _.
  move=> n; have : (0 < size (c' n))%N by rewrite size_tuple.
  by case: c' => -[//|u v/= _ _]; exists u, v.
move/choice => [u /choice[v c'_uv]].
have : forall n, exists u' v', d' n = rcons u' v' :> seq _.
  move=> n; have : (0 < size (d' n))%N by rewrite size_tuple.
  case: d' => -[//|u' v'/= _ _].
  exists (belast u' v').
  exists (last u' v').
  by rewrite lastI.
move/choice => [u' /choice[v' d'_uv]].
have sz_u' n : size (u' n) = n.
  apply: succn_inj.
  rewrite (_ : size (u' n) = (size (rcons (u' n) (v' n))).-1).
    by rewrite size_rcons.
  by rewrite -d'_uv size_tuple.
have sz_v n : size (v n) = n.
  apply: succn_inj.
  rewrite (_ : size (v n) = (size ((u n) :: (v n))).-1) //.
  by rewrite -c'_uv size_tuple.
have size_v'v n : minn (size (u' n)) (size (v n)) = n.
  by rewrite sz_u' sz_v minnn.
(* NB: second use of interleave *)
have pc'd' n : itv_partition c (c_ n n) (interleave (u' n) (v n)).
  split.
    rewrite lt_path_sortedE; apply/andP; split.
      rewrite (eq_all_r (mem_interleave _)) ?sz_u' ?sz_v//.
      rewrite all_cat; apply/andP; split.
        apply/allP => z zc'.
        rewrite (@le_lt_trans _ _ (c_ n 0))//.
          by rewrite /c_ OrderedBounds.cbE eqxx.
        move/(nthP d) : zc' => -[i].
        rewrite sz_u' => ni <-{z}.
        rewrite [ltRHS](_ : _ = nth d (rcons (u' n) (v' n)) i).
          by rewrite nth_rcons sz_u' ni.
        rewrite -d'_uv.
        rewrite [ltRHS](_ : _ = d_ n i).
          rewrite (nth_map 0) ?size_tuple//.
            exact: ltnW.
          congr (d_ n) => /=.
          have {}ni : (i < n.+1)%N.
            exact: ltnW.
          by rewrite (nth_ord_enum _ (Ordinal ni))//.
        rewrite (@le_lt_trans _ _ (c_ n i))//.
          apply/le_sorted_leq_nth => //.
          exact: ContItvs.sorted_c.
          by rewrite inE size_tuple.
          by rewrite inE size_tuple// ltnW.
        by rewrite ContItvs.cltd// ltnW.
      apply/allP => z zvn.
      rewrite (@le_lt_trans _ _ (c_ n 0))//.
        by rewrite /c_ OrderedBounds.cbE eqxx.
      rewrite (@lt_le_trans _ _ (d_ n 0))//.
        by rewrite ContItvs.cltd.
      move/(nthP d) : zvn => -[i].
      rewrite sz_v => ni <-{z}.
      rewrite -[leRHS]/(nth d (((u n) :: (v n))) i.+1).
      rewrite -c'_uv.
      rewrite (nth_map 0) ?size_tuple//.
      have {}ni : (i.+1 < n.+1)%N by [].
      rewrite (nth_ord_enum _ (Ordinal ni))//.
      rewrite /d_ OrderedBounds.daE -/(a_ _ _).
      rewrite /c_ OrderedBounds.cbE/= -/(b_ _ _).
      rewrite (@le_trans _ _ (b_ n 0)).
        rewrite OrderedBounds.a_le_b//.
        by move=> i0; exact: contiguous_itvs1_lt_contiguous_itvs2.
      apply/le_sorted_leq_nth.
      apply: OrderedBounds.sorted_seq_b => //.
        by move=> ?; exact: contiguous_itvs1_lt_contiguous_itvs2.
      exact: ContItvs.trivIsetAB.
      rewrite inE/= size_tuple.
      rewrite ltnS in ni.
      by rewrite (leq_trans _ ni).
      rewrite inE/= size_tuple.
      by rewrite ltnS in ni.
      exact: leq0n.
      done.
    apply/lt_sorted_interleaveP; rewrite ?sz_v ?sz_u'//.
    split.
      move=> i d0 ni.
      rewrite [ltLHS](_ : _ = nth d0 (d' n) i).
        by rewrite d'_uv nth_rcons sz_u' ni.
      rewrite [ltRHS](_ : _ = nth d0 (c' n) i.+1).
        by rewrite c'_uv/=.
      rewrite (nth_map 0) ?size_tuple//.
        exact: ltnW.
      have niW : (i < n.+1)%N by rewrite ltnW.
      rewrite (nth_ord_enum _ (Ordinal niW))//.
      rewrite [in ltRHS](nth_map 0) ?size_tuple//.
      rewrite -ltnS in ni.
      rewrite (nth_ord_enum _ (Ordinal ni))//=.
      by rewrite ContItvs.dltc.
    move=> i d0 ni.
    rewrite [ltLHS](_ : _ = nth d0 (c' n) i.+1).
      by rewrite c'_uv/=.
    rewrite [ltRHS](_ : _ = nth d0 (d' n) i.+1).
      by rewrite d'_uv/= nth_rcons sz_u' ni.
    rewrite (nth_map 0) ?size_tuple//.
      exact: ltnW.
    have niW : (i.+1 < n.+1)%N by rewrite ltnW.
    rewrite (nth_ord_enum _ (Ordinal niW))//.
    rewrite [in ltRHS](nth_map 0) ?size_tuple//.
    rewrite (nth_ord_enum _ (Ordinal niW))//=.
    by rewrite ContItvs.cltd.
  rewrite last_interleave.
    by rewrite sz_v sz_u'.
  rewrite /c_.
  rewrite OrderedBounds.cbE.
  case: ifPn => [/eqP n0|n0].
    have /eqP -> : v n == [::].
      rewrite -size_eq0.
      rewrite -[eqbLHS]/((size (u n :: v n)).-1).
      by rewrite -c'_uv size_tuple n0.
    by [].
  apply/eqP.
  transitivity (last c (c' n)).
    rewrite c'_uv last_cons.
    apply: set_last_default.
    by rewrite sz_v lt0n.
  rewrite -nth_last size_tuple.
  rewrite (nth_map 0) ?size_tuple//.
  rewrite (nth_ord_enum _ (Ordinal (ltnSn n)))//=.
  by rewrite /c_ OrderedBounds.cbE (negPf n0)//.
(*
 * c = c0, d0, c1, d1, ... cn, dn = d
*)

have nthcc_ n (i : 'I_n) : nth d (c :: v n) i = c_ n i.
  have [->|i0] := eqVneq (i : nat) 0.
    by rewrite /c_ OrderedBounds.cbE.
  transitivity ((c' n)`_i).
    rewrite c'_uv.
    rewrite -(@prednK i)/= ?lt0n//.
    apply: set_nth_default.
    by rewrite sz_v// prednK ?lt0n// ltnW.
  rewrite /c'/= (nth_map 0) ?size_enum_ord.
    by rewrite ltnS ltnW.
  by rewrite (nth_ord_enum ord0 (widen_ord (leqnSn n) i)).
have nthdd_ n (i : 'I_n) : nth d (u' n) i = d_ n i.
  transitivity ((d' n)`_i).
    rewrite d'_uv.
    rewrite nth_rcons sz_u' (ltn_ord i)//.
    apply: set_nth_default.
    by rewrite sz_u'// prednK ?lt0n// ltnW.
  rewrite /d'/= (nth_map 0) ?size_enum_ord.
    by rewrite ltnS ltnW.
  by rewrite (nth_ord_enum ord0 (widen_ord (leqnSn n) i)).
have nthvc_ n (i : 'I_n) : nth d (v n) i = c_ n i.+1.
  transitivity (nth d (c' n) i.+1).
    by rewrite c'_uv//=.
  rewrite /c'/= (nth_map 0) ?size_enum_ord.
    by rewrite ltnS.
  have ni : (i.+1 < n.+1)%N by rewrite ltnS.
  by rewrite (nth_ord_enum ord0 (Ordinal ni))/=.
have nthu'd_ n (i : 'I_n) : nth d (u' n) i = d_ n i.
  transitivity (nth d (d' n) i).
     by rewrite d'_uv//= nth_rcons sz_u' (ltn_ord i).
  rewrite /d'/= (nth_map 0) ?size_enum_ord.
    by rewrite ltnS ltnW.
  have ni : (i < n.+1)%N by rewrite ltnS ltnW.
  by rewrite (nth_ord_enum ord0 (Ordinal ni))/=.
have V_tv n : (V_ n <= Vcd)%E.
  rewrite /V_ /Vcd.
  rewrite (@total_variationD _ _ _ (c_ n n)).
  - by rewrite /c_ OrderedBounds.cbE; case: ifPn => // n0; exact: ContItvs.inf_le_b.
  - exact: ContItvs.c_le_sup.
  rewrite (@total_variation_interleave_split _ _ _ f ((u' n)) (v n) d d)//.
    by apply ContItvs.inf_le_c.
  rewrite addrAC leeD//.
    rewrite big_ord_recr/= leeD//.
      rewrite size_v'v.
      apply: lee_sum => i _.
      rewrite nthcc_// nthdd_//.
      apply: total_variation_ge.
      exact: ContItvs.c_le_d.
    apply: (@le_trans _ _ (total_variation (c_ n n) (d_ n n) f)).
      apply: total_variation_ge => //.
      exact: ContItvs.c_le_d.
    apply: (@total_variation_nondecreasing _ _ d).
    - by rewrite in_itv/= ContItvs.c_le_d//= ContItvs.d_le_sup.
    - by rewrite bound_itvE ContItvs.c_le_sup.
    - by rewrite ContItvs.d_le_sup.
  rewrite size_v'v lee_sum// => i _.
  rewrite nthdd_ /d_ OrderedBounds.daE -/a_.
  rewrite nthvc_.
  by rewrite /c_ OrderedBounds.cbE/=.
have cdbvf : bounded_variation c d f.
  apply: (bounded_variationl (ltW cd) db).
  apply: bounded_variationr ac _ bvf.
  by apply: ltW; exact: (lt_le_trans cd).
have Soo_tv : (S_ n)%:E @[n --> \oo] --> Vcd.
  exact: ene5 lambda0.
have Voo_V : V_ n @[n --> \oo] --> Vcd.
  apply: (squeeze_cvge _ _ _ _ _ Soo_tv) => //.
  apply: nearW => n.
  apply/andP; split.
    exact: SV.
  exact: V_tv.
(* (3) *)
have eq3 : \forall n \near \oo, (Vcd - alpha / 2 < V_ n)%E.
  have alpha20 : 0 < fine (alpha / 2).
    apply: fine_gt0; rewrite mule_gt0//=.
      by rewrite inver ifF; exact/negP/negP.
    rewrite inver ifF; first exact/negP/negP.
    by rewrite lte_mul_pinfty ?measure_ge0 ?ltry.
  move: Voo_V.
  rewrite -{1}(@fineK _ Vcd).
    by apply/bounded_variationP => //; exact: ltW.
  move/fine_cvg.
  move/(_ (ball (fine Vcd) (fine (alpha / 2))) (nbhsx_ballx _ _ alpha20)).
  move=> [n0 _ H].
  exists n0.+1 => //n n0n.
  have := H n (ltnW n0n).
  rewrite /ball/=.
  rewrite /ereal_ball/=.
  have Vcdoo : (Vcd < +oo)%E.
    rewrite -ge0_fin_numE; last by apply/bounded_variationP => //; exact: ltW.
    by apply: total_variation_ge0; exact: ltW.
  have Vn_fin : V_ n \is a fin_num.
    rewrite ge0_fin_numE.
      apply: adde_ge0.
        exact: sume_ge0.
      apply: sume_ge0 => ? _.
      apply: total_variation_ge0.
      apply: OrderedBounds.a_le_b.
      move=> i; exact: contiguous_itvs1_lt_contiguous_itvs2.
    exact: (le_lt_trans (V_tv n)).
  have al2fin : (alpha / 2)%E \is a fin_num.
    rewrite inver ifF; first exact/negP/negP.
    rewrite ge0_fin_numE.
      by rewrite mule_ge0 ?ltW.
    rewrite lte_mul_pinfty ?ltW//.
    exact: ltry.
  rewrite ger0_norm.
    rewrite subr_ge0.
    rewrite fine_le//.
      apply/bounded_variationP => //.
      exact: ltW.
  rewrite ltrBlDl -ltrBlDr.
  rewrite -fineB//.
    by apply/bounded_variationP => //; exact: ltW.
  rewrite -lte_fin !fineK//.
  rewrite fin_numB; apply/andP; split => //.
  by apply/bounded_variationP => //; exact: ltW.
(* (4) *)
(* total_variationD? *)
have eq4 n : total_variation c d f =
  \sum_(i < n.+1) (H (d_ n i) - H (c_ n i))%:E +
   \sum_(i < n) total_variation (a_ n i) (b_ n i) f.
  rewrite (@total_variationD _ _ _ (c_ n n)).
  - exact: ContItvs.inf_le_c.
  - exact: ContItvs.c_le_sup.
  rewrite (@total_variation_interleave_split _ _ _ f (u' n) (v n) d d)//.
    exact: ContItvs.inf_le_c.
  rewrite sz_u' sz_v minnn.
  rewrite /H.
  transitivity ((\sum_(i < n) total_variation (c_ n i) (d_ n i) f +
    \sum_(i < n) total_variation (d_ n i) (c_ n i.+1) f)%R +
    total_variation (c_ n n) d f)%E.
    congr (_ + _ + _) => //.
      apply: eq_bigr => /= i _.
      by rewrite nthcc_ nthdd_.
    apply: eq_bigr => /= i _.
    by rewrite nthu'd_ nthvc_.
  have lem1 (i : 'I_n.+1) :
      total_variation (c_ n i) (d_ n i) f \is a fin_num.
    apply/bounded_variationP; first exact: ContItvs.c_le_d.
    apply: bounded_variationS cdbvf => //.
    - exact: ContItvs.c_le_d.
    - exact: ContItvs.inf_le_c.
    - exact: ContItvs.d_le_sup.
  have lem2 (i : 'I_n) :
      total_variation (c_ n i) (d_ n i) f \is a fin_num.
    apply/bounded_variationP; first exact: ContItvs.c_le_d.
    apply: bounded_variationS cdbvf => //.
    - exact: ContItvs.c_le_d.
    - exact: ContItvs.inf_le_c.
    - exact: ContItvs.d_le_sup.
  have lem3 (i : 'I_n.+1) :
      total_variation a (d_ n i) f \is a fin_num.
    apply/bounded_variationP.
      by rewrite (le_trans ac)// ContItvs.inf_le_d.
    apply: bounded_variationS bvf => //.
      by rewrite (le_trans ac)// ContItvs.inf_le_d.
    by rewrite (le_trans _ db)// ContItvs.d_le_sup.
  transitivity (\sum_(i < n.+1) (fine (total_variation (c_ n i) (d_ n i) f))%:E +
      \sum_(i < n) total_variation (a_ n i) (b_ n i) f); last first.
    congr (_ + _)%E.
    apply: eq_bigr => /= i _.
    rewrite fineK.
      exact: lem1.
    rewrite EFinB fineK.
      exact: lem3.
    rewrite fineK//.
      apply/bounded_variationP.
        by rewrite (le_trans ac)// ContItvs.inf_le_c.
      apply: bounded_variationS bvf => //.
        by rewrite (le_trans ac)// ContItvs.inf_le_c.
      by rewrite (le_trans _ db)// ContItvs.c_le_sup.
    apply/eqP.
    rewrite eq_sym sube_eq.
    - exact: lem3.
    - rewrite fin_num_adde_defr.
      exact: lem1.
      by [].
    rewrite addrC -total_variationD//.
      by rewrite (le_trans ac)//; exact: ContItvs.inf_le_c.
    exact: ContItvs.c_le_d.
  rewrite big_ord_recr/=.
  rewrite [in RHS]addrAC.
  congr (_ + _ + _)%E.
  - apply: eq_bigr => i _.
    rewrite fineK.
      exact: lem2.
      by [].
  - apply: eq_bigr => i _.
    rewrite /d_ OrderedBounds.daE -/a_.
    by rewrite /c_ OrderedBounds.cbE/= -/b_.
  - rewrite /d_ OrderedBounds.daE OrderedBounds.a_default//.
    rewrite fineK//.
    apply/bounded_variationP; first exact: ContItvs.c_le_sup.
    apply: bounded_variationS cdbvf => //.
    - exact: ContItvs.c_le_sup.
    - exact: ContItvs.inf_le_c.
have absubcd n i : (i < n)%N ->  `[a_ n i, b_ n i] `<=` `[c, d].
  move=> iltn.
  rewrite -[in X in X `<=` _]setU_1itvob ?bnd_simp//.
    apply: OrderedBounds.a_le_b => k.
    exact: contiguous_itvs1_lt_contiguous_itvs2.
  rewrite -[in X in X `<=` _]setU_itvob1 ?bnd_simp//.
    apply: OrderedBounds.a_lt_b => // k.
    exact: contiguous_itvs1_lt_contiguous_itvs2.
  rewrite 2!subUset; split.
    by rewrite sub1set inE/= in_itv/= ContItvs.inf_le_a//= ContItvs.a_le_sup.
  split; last first.
    by rewrite sub1set inE/= in_itv/= ContItvs.inf_le_b//= ContItvs.b_le_sup.
  apply: subset_itv; rewrite bnd_simp.
    exact: ContItvs.inf_le_a.
  exact: ContItvs.b_le_sup.
  (*
  rewrite -contiguous_ooitv//.
  rewrite -compact_Rhull//.
  apply: (subset_trans (@contiguous_itvsS _ Z (h1 i))).
  exact: cplt_hull_subset_Rhull.
  *)
have ABbvf n : \sum_(i < n) total_variation (a_ n i) (b_ n i) f \is a fin_num.
  apply/sum_fin_numP => /=.
  case => i iltn1 _ _.
  destruct n => //.
  rewrite -(inord_val (Ordinal _))/= !inordK//.
  apply/bounded_variationP.
    apply: OrderedBounds.a_le_b => ?.
    exact: contiguous_itvs1_lt_contiguous_itvs2.
  apply: (@bounded_variationr _ c).
  - (* generalize incl_itv_lb? *)
    (* a < b -> `]a, b[ `<=` `[c, d] -> a < c *)
    rewrite leNgt; apply/negP => cA.
    move: (absubcd n.+1 i iltn1).
    move/disj_setPCl/disj_set2P.
    apply/eqP/set0P.
    have [bc|cb] := leP (b_ n.+1 i) c.
      exists (((a_ n.+1 i) + (b_ n.+1 i)) / 2) => /=; split.
        rewrite in_itv/= !midf_le -/(a_ n.+1 i)//.
          apply: OrderedBounds.a_le_b => k.
          exact: contiguous_itvs1_lt_contiguous_itvs2.
        rewrite OrderedBounds.a_le_b// => k.
        exact: contiguous_itvs1_lt_contiguous_itvs2.
      apply/negP; rewrite in_itv/= negb_and -ltNge; apply/orP; left.
      rewrite -/c (@splitr _ c).
      rewrite mulrDl.
      by rewrite ltr_leD ?ltr_pM2r ?ler_pM2r.
    exists ((a_ n.+1 i + c) / 2) => /=; split; rewrite in_itv/=.
      rewrite !midf_le// ?ltW// (@splitr _ (b_ n.+1 i)) mulrDl ltrD ?ltr_pM2r//.
      apply: OrderedBounds.a_lt_b => // k.
      exact: contiguous_itvs1_lt_contiguous_itvs2.
    apply/negP; rewrite negb_and -ltNge; apply/orP; left.
    by rewrite -/c midf_lt.
  - apply: OrderedBounds.a_le_b => k.
    exact: contiguous_itvs1_lt_contiguous_itvs2.
  apply: bounded_variationl cdbvf.
  rewrite leNgt; apply/negP => Bc.
  move: (absubcd n.+1 i iltn1).
  move/disj_setPCl/disj_set2P.
  apply/eqP/set0P.
  exists (((a_ n.+1 i) + (b_ n.+1 i)) / 2) => /=; split.
    rewrite in_itv/= !midf_le// OrderedBounds.a_le_b// => k;
      exact: contiguous_itvs1_lt_contiguous_itvs2.
    apply/negP; rewrite in_itv/= negb_and -ltNge; apply/orP; left.
    rewrite -/c (@splitr _ c) mulrDl ltrD ?ltr_pM2r//.
    rewrite (le_lt_trans _ Bc)//.
    apply: OrderedBounds.a_le_b => k.
    exact: contiguous_itvs1_lt_contiguous_itvs2.
  (* generalize incl_itv_ub? *)
  (* a < b -> `]a, b[ `<=` `[c, d] -> b < d *)
  rewrite leNgt; apply/negP => dB.
  move: (absubcd n.+1 i iltn1).
  move/disj_setPCl/disj_set2P.
  apply/eqP/set0P.
  have [ad|da] := leP d (a_ n.+1 i).
    exists (((a_ n.+1 i) + (b_ n.+1 i)) / 2) => /=; split.
      by rewrite in_itv/= !midf_le// OrderedBounds.a_le_b// => k;
        exact: contiguous_itvs1_lt_contiguous_itvs2.
    apply/negP; rewrite in_itv/= negb_and -!ltNge; apply/orP; right.
    rewrite (@splitr _ d).
    rewrite mulrDl.
    by rewrite ler_ltD ?ltr_pM2r ?ler_pM2r.
  exists ((d + b_ n.+1 i) / 2) => /=; split; rewrite in_itv/=.
    rewrite !midf_le// ?ltW// (@splitr _ (a_ n.+1 i)) mulrDl ltrD ?ltr_pM2r//.
    rewrite OrderedBounds.a_lt_b// => k.
    exact: contiguous_itvs1_lt_contiguous_itvs2.
  apply/negP; rewrite negb_and -!ltNge; apply/orP; right.
  by rewrite midf_lt.

(* (5) *)
have eq5 : \forall n \near \oo,
  (\sum_(i < n.+1) (H (d_ n i) - H (c_ n i))%:E - (alpha / 2) <
  \sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)|%:E)%E.
  move: eq3 => [n0 _/= hyp].
  exists n0 => // n/= n0n.
  move: (hyp n n0n) => {hyp}.
  rewrite /V_ -lteBlDr.
    by case: n n0n.
  rewrite /Vcd (eq4 n).
    apply: le_lt_trans.
    rewrite addeAC leeB// -addeA leeDl// subre_ge0.
    exact: ABbvf.
  done.
(* (5.5) (between (5) and (6)) *)
have alphaH n : (alpha <= \sum_(i < n.+1) (H (d_ n i) - H (c_ n i))%:E)%E.
  rewrite /alpha.
  apply: (@le_trans _ _ (mu (H @` (\bigcup_(i < n.+1) `[c_ n i, d_ n i]%classic)))).
    apply: le_outer_measure.
    apply: image_subset.
    exact: ContItvs.Zcd.
  rewrite image_bigcup.
  rewrite bigcup_mkord.
  rewrite [leRHS](_ : _ = \sum_(i < n.+1) mu `[H (c_ n i), H (d_ n i)]).
    apply: eq_bigr => i _.
    have : H (c_ n i) <= H (d_ n i).
      apply: ndH.
      - rewrite in_itv/=; apply/andP; split.
          by rewrite (le_trans ac)// ContItvs.inf_le_c.
        by rewrite (le_trans _ db)// ContItvs.c_le_sup.
      - rewrite in_itv/=; apply/andP; split.
          by rewrite (le_trans ac)// ContItvs.inf_le_d.
        rewrite (le_trans _ db)//.
        by rewrite /d_ OrderedBounds.daE -/(a_ _) ContItvs.a_le_sup.
      - exact: ContItvs.c_le_d.
    rewrite le_eqVlt => /predU1P[->|Hcd].
      by rewrite subrr lebesgue_measure_itv/= ltxx.
    by rewrite lebesgue_measure_itv/= lte_fin Hcd EFinD.
  apply: (@le_trans _ _
    (\sum_(i < n.+1) mu [set H x | x in `[c_ n i, d_ n i]])).
    exact: (outer_measure_subadditive mu
       (fun i => [set H x | x in `[c_ n i, d_ n i]])).
  apply: lee_sum => i _.
  apply: le_outer_measure.
  apply: continuous_nondecreasing_image_itvcc.
  - exact: ContItvs.c_le_d.
  - apply: continuous_subspaceW cH.
    apply: subset_itv; rewrite bnd_simp.
    rewrite (le_trans ac)// ContItvs.inf_le_c//=.
    by rewrite (le_trans _ db)// ContItvs.d_le_sup.
  move=> x y xcd ycd xy.
  apply: (bounded_variation_total_nondecreasing bvf _ _ xy).
    apply: subset_itv xcd; rewrite bnd_simp.
    rewrite (le_trans ac)// ?ContItvs.inf_le_c//=.
    by rewrite (le_trans _ db)// ContItvs.d_le_sup.
  apply: subset_itv ycd; rewrite bnd_simp.
  rewrite (le_trans ac) ?ContItvs.inf_le_c//=.
  by rewrite (le_trans _ db)// ContItvs.d_le_sup.
(*
rewrite addrAC ltrD2r.
move/(@lt_trans _ _ _ (fine alpha / 2)).
rewrite addrA.
rewrite ltrBrDl -splitr; move/(_ alphaH).
*)
(* (6) *)
have ineq6 : \forall n \near \oo,
    (alpha / 2 < \sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)|%:E)%E.
  have [n0 _ /= H5] := eq5.
  exists n0 => // n/= n0n.
  apply: le_lt_trans (H5 n n0n).
  rewrite leeBrDl.
    by rewrite fin_numM// fin_numV.
  rewrite -mule2n -mule_natr.
  rewrite muleAC -muleA divee// mule1.
  exact: alphaH.
have cdIcplt_hull (S : set R) : measurable S -> S `<=` `[c, d] ->
                                mu S = mu (S `&` cplt_hull Z).
  move=> mS Scd.
  rewrite -[in LHS](setIidl Scd).
  rewrite -compact_Rhull//.
  have -> : [set` Rhull Z] = Z `|` cplt_hull Z.
    rewrite -(setUIDK [set` Rhull Z] Z); congr setU.
    apply: setIidr.
    exact: sub_Rhull.
  rewrite setIUr.
  rewrite measureU/=.
  - apply: measurableI => //.
    exact: compact_measurable.
  - apply: measurableI => //.
    apply: measurableD => //.
    exact: compact_measurable.
  - by rewrite setIACA setDIK setI0.
    rewrite -[RHS]add0e; congr +%E.
    apply/eqP; rewrite -measure_le0/=.
    rewrite -Z0.
    apply: le_outer_measure.
    exact: subIsetr.
(* (6.5) (between (6) and (7)) *)
pose ABcd n (i : 'I_ n.+1) := [set k | `]A_ k, B_ k[ `<=` `[c_ n i, d_ n i]].
(* have UABcdE n : \bigcup_(i < n.+1) (ABcd _ i) = [set k | n < k]. *)
set Zsub := fun n (i : 'I_ n.+1) => Z `&` `[c_ n i, d_ n i].
have hull_Zsub n (i : 'I_ n.+1) :
  [set` Rhull (Zsub n i)] `<=` `[c_ n i, d_ n i]%classic.
  rewrite Rhull_smallest.
  apply: smallest_sub; first exact: interval_is_interval.
  exact: subIsetr.
have cf_cd n i : {within `[c_ n i, d_ n i], continuous f}.
  apply: continuous_subspaceW cf.
  apply: subset_itv; rewrite bnd_simp.
    apply: (le_trans ac).
    rewrite /c_ OrderedBounds.cbE; case: i => //= i.
    apply: (@le_trans _ _ (OrderedBounds.a_ A_ B_ d n i)).
      exact: ContItvs.inf_le_a.
    apply: OrderedBounds.a_le_b => // i0.
    exact: contiguous_itvs1_lt_contiguous_itvs2.
  apply: (le_trans _ db).
  rewrite /d_ OrderedBounds.daE.
  apply: (@le_trans _ _ (OrderedBounds.b_ A_ B_ d n i)).
    apply: OrderedBounds.a_le_b => // i0.
    exact: contiguous_itvs1_lt_contiguous_itvs2.
  exact: ContItvs.b_le_sup.
have itvfcd n (i : 'I_ n.+1) : is_interval (f @` `[c_ n i, d_ n i]).
  apply: (is_interval_image_cc cf).
  apply: subset_itv => //; rewrite bnd_simp.
    apply: (le_trans ac).
    rewrite [leRHS]OrderedBounds.cbE; case: i; case => //= i _.
    apply: (@le_trans _ _ (OrderedBounds.a_ A_ B_ d n i)).
      exact: ContItvs.inf_le_a.
    apply: OrderedBounds.a_le_b => // i0.
    exact: contiguous_itvs1_lt_contiguous_itvs2.
  apply: le_trans db.
  rewrite /d_ OrderedBounds.daE.
  apply: (@le_trans _ _ (OrderedBounds.b_ A_ B_ d n i)).
    apply: OrderedBounds.a_le_b => // i0.
    exact: contiguous_itvs1_lt_contiguous_itvs2.
  exact: ContItvs.b_le_sup.
have Zsub_cover n (i : 'I_ n.+1) : `[c_ n i, d_ n i]%classic `<=`
    Zsub n i `|` \bigcup_(i0 in [set k | `[A_ (n + k)%N, B_ (n + k)%N] `<=` `[c_ n i, d_ n i] ])
    `](A_ (n + i0)%N), B_ (n + i0)%N[%classic.
  move=> x/= cdx.
  have : [set` Rhull Z] x.
    rewrite (ContItvs.hullZ_abcd lbZ ubZ h1 n cd cZ Z_nonempty); left.
    by exists i => /=.
  rewrite -(setUIDK [set` Rhull Z] Z).
  rewrite setIidr -/(cplt_hull Z); first exact: sub_Rhull.
  move=> [Zx|].
    by left.
  rewrite cplt_hull_contiguous_itvs//.
  rewrite bigcup_contiguous_itvs_support.
  have [funh1 injh1 surjh1] := @bij _ _ _ _ h1.
  rewrite (reindex_bigcup h1 _ _ _ funh1 surjh1).
  move=> [k _ kx].
  have nk : (n <= k)%N.
    rewrite leqNgt; apply/negP => kn1.
    move: (ContItvs.disj_abcd lbZ ubZ h1 n).
    apply/eqP/set0P; exists x; split.
      by exists i => /=.
    by exists k => /=.
  right.
  exists (k - n)%N => /=.
    rewrite subnKC//.
    apply: subset_neitv_oocc => //.
      by apply: contiguous_itvs1_lt_contiguous_itvs2.
(* lemma *)
    move=> z /[dup] ABkz.
    rewrite /A_ /B_ -contiguous_ooitv// => kz.
    have [j jn2 cdjz/=] := ContItvs.citvScd_tmp lbZ ubZ cZ Z_nonempty kz nk.
    rewrite -/(c_ _ _) -/(d_ _ _) in cdjz.
    suff -> : i = j :> nat by [].
    apply/not_notP => /eqP ij.
    have [|zx] := leP x z.
      move=> xz.
      have {}ij : (i < j)%N.
        rewrite ltnNge; apply/negP => ji.
        have djci : d_ n j <= c_ n i.
          rewrite /d_ /c_.
          rewrite OrderedBounds.cbE OrderedBounds.daE.
          have [i0|i0] := eqVneq i 0.
            subst i.
            rewrite leqn0 in ji.
            by rewrite (eqP ji) eqxx in ij.
          rewrite [in leRHS]ifF.
            by apply/negbTE.
          rewrite /OrderedBounds.a_ /OrderedBounds.b_.
          apply: (@le_trans _ _ (b_ n j)).
            apply: OrderedBounds.a_le_b => //= j0.
            by apply: contiguous_itvs1_lt_contiguous_itvs2.
          rewrite /b_.
          rewrite /OrderedBounds.b_.
          rewrite leq_eqVlt eq_sym (negPf ij) /= in ji.
          apply/sorted_leq_nth => //.
          - exact: le_trans.
          - apply: OrderedBounds.sorted_seq_b => //.
              by move=> j0; exact: contiguous_itvs1_lt_contiguous_itvs2.
            exact: ContItvs.trivIsetAB.
            rewrite inE size_tuple.
            by rewrite (leq_trans ji)// -ltnS.
            rewrite inE size_tuple.
            by rewrite prednK// ?lt0n// -ltnS.
          - rewrite -subn1 leq_subCr ?lt0n// 1?ltnW//.
            by rewrite subn_eq0 -ltnNge.
        have cidj : c_ n i <= d_ n j.
          move: cdx cdjz; rewrite !in_itv/= => /andP[cix xdi] /andP[cjz zdj].
          by rewrite (le_trans cix)// (le_trans xz)//.
        have /eqP : d_ n j = c_ n i.
          by apply/eqP; rewrite eq_le djci cidj.
        rewrite lt_eqF//.
        apply: ContItvs.dltc => //.
        rewrite -subn1 ltn_psubLR//.
        destruct n => //.
        rewrite ltnS leqn0 in jn2.
        by rewrite (ord1 i) (eqP jn2) eqxx in ij.
        by rewrite ltn_neqAle eq_sym ij ji.
      have [l ilj [H1 H2]] : exists2 l, (i <= l < j)%N & (d_ n i <= a_ n l <= b_ n l /\ b_ n l <= c_ n j).
        exists i; first by rewrite leqnn ij.
        split.
          rewrite /d_ OrderedBounds.daE lexx/=.
          apply: OrderedBounds.a_le_b => // i0.
          exact: contiguous_itvs1_lt_contiguous_itvs2.
        rewrite /c_ OrderedBounds.cbE ifF.
          by apply/negbTE; rewrite -lt0n (leq_trans _ ij).
        apply/sorted_leq_nth => //.
        exact: le_trans.
        apply: OrderedBounds.sorted_seq_b => //.
          by move=> ?; exact: contiguous_itvs1_lt_contiguous_itvs2.
        exact: ContItvs.trivIsetAB.
        by rewrite !inE size_tuple (ltn_leq_trans ij).
        by rewrite !inE size_tuple prednK// (leq_ltn_trans _ ij).
        by rewrite -ltnS prednK (leq_ltn_trans _ ij).
      have xzk : `[x, z]%classic `<=` contiguous_itvs Z (h1 k).
        move=> t/= txz.
        have := @is_interval_contiguous_itvs _ Z (h^-1%FUN k) _ _ kx kz t.
        by rewrite !(itvP txz) => /(_ isT).
      have : `]a_ n l, b_ n l[ `<` contiguous_itvs Z (h1 k).
        apply: (proper_subset_trans _ xzk).
        apply/proper_itvoo_cc.
        apply: OrderedBounds.a_lt_b.
          by move=> ?; exact: contiguous_itvs1_lt_contiguous_itvs2.
        by move/andP : ilj => [_ /ltn_leq_trans]; apply; rewrite -ltnS.
        split.
          rewrite (@le_trans _ _ (d_ n i)); last by move/andP : H1 => [].
            by rewrite (itvP cdx).
          by move/andP : H1 => [].
        rewrite (@le_trans _ _ (c_ n j)); last by move/andP : H1 => [].
        by [].
        by rewrite (itvP cdjz).
      rewrite /a_ OrderedBounds.anth.
      rewrite /b_ OrderedBounds.bnth.
      have ln : (l < n)%N.
        move : ilj => /andP[_ /ltn_leq_trans]; apply.
        by rewrite -ltnS.
      have [-> -> ?] := ListOfBounds.nth_abiE A_ B_ d ln.
      rewrite /A_ /B_/=.
      rewrite -contiguous_ooitv//.
      apply: contiguous_itvs_not_nested.
      exact: funh1.
    have {}ij : (j < i)%N.
      rewrite ltnNge; apply/negP => ji.
      have dicj : d_ n i <= c_ n j.
        rewrite /d_ /c_.
        rewrite OrderedBounds.cbE OrderedBounds.daE.
        have [j0|j0] := eqVneq j 0.
          subst j.
          rewrite leqn0 in ji.
          by rewrite (eqP ji) eqxx in ij.
        apply: (@le_trans _ _ (a_ n j.-1)); last first.
          apply: OrderedBounds.a_le_b => //=.
          by move=> i0; apply: contiguous_itvs1_lt_contiguous_itvs2.
        rewrite -/a_.
        rewrite leq_eqVlt (negbTE ij)/= in ji.
        apply/sorted_leq_nth => //.
        - exact: le_trans.
        - exact: ListOfBounds.sorted_seq_a.
          by rewrite inE size_tuple (ltn_leq_trans ji).
          by rewrite inE size_tuple prednK// ?lt0n// -ltnS.
          by rewrite -ltnS prednK// lt0n.
      have cjdi : c_ n j <= d_ n i.
        move: cdx cdjz; rewrite !in_itv/= => /andP[cix xdi] /andP[cjz zdj].
        by rewrite (le_trans cjz)// (le_trans (ltW zx)).
      have /eqP : d_ n i = c_ n j.
        by apply/eqP; rewrite eq_le cjdi dicj.
      rewrite lt_eqF//.
      apply: ContItvs.dltc => //.
      rewrite -subn1.
      rewrite ltn_psubLR//.
      destruct n => //.
      rewrite ltnS leqn0 in jn2.
      by rewrite (ord1 i) (eqP jn2) eqxx in ij.
      by rewrite ltn_neqAle ij ji.
    have [l ilj [H1 H2]] : exists2 l, (j <= l < i)%N & (d_ n j <= a_ n l <= b_ n l /\ b_ n l <= c_ n i).
      exists j; first by rewrite leqnn ij.
      split.
        apply/andP; split.
          by rewrite /d_ OrderedBounds.daE.
          apply: OrderedBounds.a_le_b => // i0.
        exact: contiguous_itvs1_lt_contiguous_itvs2.
      rewrite /c_ OrderedBounds.cbE ifF.
        by apply/negbTE; rewrite -lt0n (leq_trans _ ij).
      apply/sorted_leq_nth => //.
      exact: le_trans.
      apply: OrderedBounds.sorted_seq_b => //.
      by move=> i0; exact: contiguous_itvs1_lt_contiguous_itvs2.
      exact: ContItvs.trivIsetAB.
      by rewrite !inE !size_tuple (ltn_leq_trans ij)// -ltnS.
      by rewrite !inE !size_tuple prednK// ?(leq_ltn_trans _ ij)// -ltnS.
      by rewrite -ltnS prednK// (leq_ltn_trans _ ij).
    have xzk : `[z, x]%classic `<=` contiguous_itvs Z (h1 k).
      move=> t/= txz.
      have := @is_interval_contiguous_itvs _ Z (h^-1%FUN k) _ _ kz kx t.
      by rewrite !(itvP txz) => /(_ isT).
    have : `]a_ n l, b_ n l[ `<` contiguous_itvs Z (h1 k).
      apply: (proper_subset_trans _ xzk).
      apply/proper_itvoo_cc.
      apply: OrderedBounds.a_lt_b.
        by move=> ?; exact: contiguous_itvs1_lt_contiguous_itvs2.
      by move/andP : ilj => [_ /ltn_leq_trans]; apply; rewrite -ltnS.
      split.
        rewrite (@le_trans _ _ (d_ n j)); last by move/andP : H1 => [].
          by rewrite (itvP cdjz).
        by move/andP : H1 => [].
      rewrite (@le_trans _ _ (c_ n i)); last by move/andP : H1 => [].
      by [].
      by rewrite (itvP cdx).
    rewrite /a_ OrderedBounds.anth.
    rewrite /b_ OrderedBounds.bnth.
    have ln : (l < n)%N.
      move : ilj => /andP[_ /ltn_leq_trans]; apply.
      by rewrite -ltnS.
    have [-> -> ?] := ListOfBounds.nth_abiE A_ B_ d ln.
    rewrite /A_ /B_/=.
    rewrite -contiguous_ooitv//.
    apply: contiguous_itvs_not_nested.
    exact: funh1.
  rewrite subnKC//.
  move: kx.
  by rewrite contiguous_ooitv.
have disj_cd n : trivIset (`I_ n.+1) (fun i => `[c_ n i, d_ n i]%classic).
  apply: ContItvs.disj_cd => //.
  exact: ContItvs.trivIsetAB.
(* (7) *)
have ineq7 n : ((\sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)|)%:E <=
  \sum_(n <= i <oo) oscillation f `[A_ i, B_ i])%E.
  have prop65 : forall i : 'I_ n.+1, (`|f (d_ n i) - f (c_ n i)|%:E <=
    \sum_(n <= j <oo | `[< `[A_ j, B_ j] `<=` `[c_ n i, d_ n i] >])
     oscillation f `[A_ j, B_ j])%E.
    move => i.
(* change to ene4_cover *)
    have /andP[le1 le2] := @ene4_cover _ _ _ (ContItvs.c_le_d lbZ ubZ h1 cZ Z_nonempty n i) f _
    (fun k : nat => (A_ (n + k)%N, B_ (n + k)%N)) (cf_cd n i)
    (itvfcd n i) (hull_Zsub n i)
    (fun k => contiguous_itvs1_le_contiguous_itvs2 (h1 (n + k)) lbZ ubZ)
    (Zsub_cover n i).
    rewrite /=.
    apply: (le_trans le1); apply: (le_trans le2).
    have -> : mu [set f x | x in Zsub n i] = 0.
      apply: lusinf.
      - by apply: subIset; left.
      - rewrite /=.
        apply: sub_caratheodory.
        rewrite RGenOpenSets.measurableE.
        apply: measurableI => //.
        exact: compact_measurable.
      apply/eqP; rewrite -measure_le0/=.
      by rewrite -Z0; apply: le_outer_measure; apply: subIsetl.
    rewrite add0r/=.
    rewrite [leLHS](_: _ =
      \big[+%E/0%R]_(n <= i0 <oo | `[< `[A_ i0, B_ i0] `<=` `[c_ n i, d_ n i] >])
      oscillation f `[A_ i0, B_ i0]).
    (* rewrite cvg_shiftn. *)
      rewrite eseries_mkcond [RHS]eseries_mkcond.
      rewrite -(nneseries_addn n).
        by move=> k; case: ifP => // _; apply: oscillation_ge0.
      apply: eq_eseriesr => k _; case: ifP => /asboolP Hk.
        by rewrite addnC ifT//; apply/asboolP; rewrite addnC.
      by rewrite ifF//; apply/asboolP; rewrite addnC.
    by apply: lee_nneseries => // j _ _; exact: oscillation_ge0.
  apply: (@le_trans _ _
    (\sum_(i < n.+1)
      \big[+%E/0%R]_(n <= i0 <oo | `[< `[A_ i0, B_ i0] `<=` `[c_ n i, d_ n i] >])
          oscillation f `[A_ i0, B_ i0])%E).
  by rewrite -sumEFin; apply: lee_sum => /= i _.
  (* interchange *)
  have : (\sum_(i < n.+1)
       \big[+%E/0]_(n <= i0 <oo | `[< `[A_ i0, B_ i0] `<=` `[c_ n i, d_ n i] >])
         oscillation f `[A_ i0, B_ i0] <=
           \sum_(n <= i0 <oo)
              (\sum_(i < n.+1 | `[< `[A_ i0, B_ i0] `<=` `[c_ n i, d_ n i] >])
       oscillation f `[A_ i0, B_ i0]))%E.
  under eq_bigr do rewrite eseries_mkcond.
  rewrite -nneseries_sum.
    move=> i j _.
    by case: ifP => // _; exact: oscillation_ge0.
  apply: lee_nneseries.
  - move=> i ni _.
    apply: sume_ge0 => j _.
    by case: ifP => // _; exact: oscillation_ge0.
  - by move=> i _; rewrite -big_mkcond; apply: lee_sum.
  move/le_trans; apply.
  rewrite eseries_cond [leRHS]eseries_cond/=.
  apply: lee_nneseries.
    by move=> i ni _; apply: sume_ge0 => j _; exact: oscillation_ge0.
  move=> j nj.
  have : supp (h1 j).
    have [+ _ _] := @bij _ _ _ _ h1.
    exact.
  move=> [z jz].
  have [k [kn1 jk]] := ContItvs.citvScd lbZ ubZ h1 cZ Z_nonempty nj.
  rewrite (bigD1_ord (Ordinal kn1))/=.
    apply/asboolP.
    apply: subset_neitv_oocc => //.
    exact: contiguous_itvs1_lt_contiguous_itvs2.
  rewrite big1; last by rewrite adde0.
  move=> i /asboolP ji.
  exfalso.
  move: ji.
  apply/existsNP; exists z.
  apply/not_implyP; split.
    move: jz.
    rewrite contiguous_ooitv//.
    exact: subset_itv_oo_cc.
  rewrite /=.
  have kj := neq_bump k i.
  move=> zbump.
  have/trivIsetP/(_ k (bump k i))/= := disj_cd n.
  move/(_ kn1).
  have bumpn2 : (bump k i < n.+1)%N.
    rewrite /bump -[ltnRHS]add1n -addnS leq_add//.
    by case: (k <= i)%N.
  move/(_ bumpn2 kj).
  move/eqP; apply/negP/set0P; exists z; split => //.
  apply: jk.
  by rewrite -contiguous_ooitv.
(* (8), used in the last step *)
have ineq8 : \forall n \near \oo,
  (alpha / 2 <= \sum_(n <= j <oo) oscillation f `[A_ j, B_ j])%E.
  have [n _ H6] := ineq6.
  exists n => // n0 /= n0n.
  apply: (le_trans _ (ineq7 n0)).
  apply: ltW.
  apply: (lt_le_trans (H6 n0 n0n)).
  by rewrite sumEFin.
(* (9), used in the last step *)
have eq9 :
   (\sum_(n <= j <oo) oscillation f `[A_ j, B_ j])%E @[n --> \oo] --> 0%:E.
(*  rewrite (cvg_shiftS (fun k => \big[+%E/0]_(k <= j <oo) _)).*)
  apply: nneseries_tail_cvg.
    apply: (@le_lt_trans _ _ Vcd).
      (* oscillation_closure *)
      have A_B_cd : forall n : nat, `[A_ n, B_ n] `<=` `[c, d].
        move=> n.
        apply: subset_itv; rewrite bnd_simp.
          rewrite /A_.
          apply: inf_contiguous_itvs1 => //.
          rewrite inE//=.
          have [+ _ _] := @bij _ _ _ _ h1.
          exact.
        rewrite /A_.
        apply: sup_contiguous_itvs2 => //.
        rewrite inE//=.
        have [+ _ _] := @bij _ _ _ _ h1.
        exact.
      rewrite [leLHS](_ : _ = (\big[+%E/0%R]_(0 <= k <oo) oscillation f `]A_ k, B_ k[)).
        apply: eq_eseriesr => i _.
        rewrite -[in RHS]oscillation_closure.
          rewrite closure_neitv_oo//.
          exact: contiguous_itvs1_lt_contiguous_itvs2.
          apply: (continuous_subspaceW _ cf).
          by move=> x /A_B_cd; apply: subset_itv; rewrite bnd_simp//.
        rewrite closure_neitv_oo//.
        exact: contiguous_itvs1_lt_contiguous_itvs2.
      apply: sum_oscillation_le_total_variation.
        exact: cd.
        exact: cdcf.
        by move=> i0; exact: contiguous_itvs1_lt_contiguous_itvs2.
        rewrite /A_ /B_.
        rewrite [X in _ _ X](_: _ = (contiguous_itvs Z) \o h1).
          by apply/funext => i; rewrite -contiguous_ooitv.
        rewrite trivIset_comp.
          by apply: set_bij_inj; apply: bij.
        apply: (@sub_trivIset _ _ _ setT) => //.
        exact: disjoint_contiguous_itvs.
        exact: A_B_cd.
    have/(bounded_variationP _ (ltW cd)) := cdbvf.
    by rewrite ge0_fin_numE// total_variation_ge0// ltW.
  move=> n _.
  exact: oscillation_ge0.
(* the last step *)
have : (alpha / 2 <= 0%:E)%E.
  have/cvg_lim <- := eq9.
    exact: ereal_hausdorff.
  apply: (lime_ge _ ineq8).
  by apply/cvg_ex; exists 0%:E.
rewrite pmule_lle0 ?inve_gt0//.
apply/negP.
by rewrite -ltNge.
Unshelve. all: end_near.
all: exact: [::].
Qed.

End ene6_direct.
End Ene6_direct.
