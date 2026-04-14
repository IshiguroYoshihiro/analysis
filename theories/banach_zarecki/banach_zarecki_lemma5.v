From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_boot all_order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import unstable.
From mathcomp Require Import mathcomp_extra boolp contra classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype derive.
From mathcomp Require Import sequences measure lebesgue_measure numfun realfun.
From mathcomp Require Import absolute_continuity.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 5)                                         *)
(*                                                                            *)
(* ```                                                                        *)
(*    mesh a b s == mesh of the partition s over [a, b]                       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma sorted_rconsE {T : eqType} (leT : rel T) :
  transitive leT ->
  forall {x : T} {s : seq T},
  sorted leT (rcons s x) = sorted leT s && all (leT ^~ x) s.
Proof.
move=> tr x s.
rewrite -rev_sorted rev_rcons/= path_sortedE; last exact: rev_trans.
by rewrite all_rev rev_sorted andbC.
Qed.

Lemma le_sorted_rconsE d {R : porderType d} (x : R) (s : seq R) :
  sorted <=%O (rcons s x) = sorted <=%O s && all (<=%O ^~ x) s.
Proof. rewrite sorted_rconsE//; exact: le_trans. Qed.

Lemma lt_sorted_rconsE d {R : porderType d} (x : R) (s : seq R) :
  sorted <%O (rcons s x) = sorted <%O s && all (<%O ^~ x) s.
Proof. rewrite sorted_rconsE//; exact: lt_trans. Qed.

Lemma path_merge {R : realType} (a : R) s h :
  a < h ->
  path <%R a s -> path <=%R a (merge <%R s [:: h]).
Proof.
elim: s a h => [a h ah _/=|s0 s1 ih a h ah].
  by rewrite ltW// andbT.
rewrite /= => /andP[as0 s0s1].
case: ifPn => s0h /=.
  by rewrite (ltW as0)/= ih.
rewrite (ltW ah)/=.
rewrite leNgt/= s0h/=.
by apply: sub_path s0s1 => x y /ltW.
Qed.

(* PR? *)
Lemma path_ltW d {T : orderType d} (a : T) s : path <%O a s -> path <=%O a s.
Proof.
rewrite le_path_pairwise lt_path_pairwise => H.
apply: (@sub_in_pairwise _ (fun x => x \in [set: T]) _ _ _ _ _ H).
  move=> x y _ _; exact: ltW.
apply/allP => x _; exact: in_setT.
Qed.

Section merge_lemmas.
Context {T : Type} {r : rel T}.
Implicit Type (s t : seq T).

Lemma merge0r s : merge r s [::] = s.
Proof. by elim: s. Qed.

End merge_lemmas.

Section merge_lemmas_eqType.
Context {T : eqType} {r : rel T}.
Implicit Types (s t : seq T) (x : T).

(* unused *)
Lemma merger_cons s t x : all (r x) t ->
  merge r (x :: s) t = x :: merge r s t.
Proof.
elim: t.
  by rewrite 2!merge0r.
move=> b t' IH.
move/allP => allxt.
rewrite /=.
rewrite ifT//.
apply: allxt.
exact: mem_head.
Qed.

(* unused *)
Lemma merge_cons_mergel s t x :
  transitive r ->
  all (r x) t -> merge r s (x :: t) = merge r (merge r s [:: x]) t.
Proof.
move=> transr.
elim: s => /=.
  elim: t => // b t' IHt.
  rewrite /= => /andP[rxb rbt'].
  by rewrite rxb.
move=> a s' IH pxt.
case: ifP.
- rewrite (IH pxt).
  move=> rax.
  rewrite merger_cons//.
  apply/allP => z zt.
  apply: (@transr x _ _ rax).
  by have /allP := pxt; exact.
- move=> raxf.
  by rewrite merger_cons.
Qed.

Lemma subseq_mergel s t :
   subseq s (merge r s t).
Proof.
elim: s t => [t|a l ih t]; first exact: sub0seq.
elim: t l ih => // t0 t1 ih s IH.
rewrite /=; case: ifPn => rat0.
  by rewrite /= eqxx IH.
rewrite /=; case: ifPn => [/eqP|] at0.
  move: rat0; rewrite -{}at0 {t0} => raa.
  rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
  exact: (subseq_trans (subseq_cons _ _) (ih s IH)).
rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
exact: ih.
Qed.

Lemma subseq_merger s t : transitive r ->
  sorted r t -> subseq t (merge r s t).
Proof.
move=> rtrans.
elim: t s => [s _|t0 t1 ih s]; first exact: sub0seq.
elim: s t0 t1 ih => // s0 s1 ih t0 t1 IH t0t1.
rewrite /=; case: ifPn => rs0t0.
  rewrite /=; case: ifPn => [/eqP ->|t0s0]; last exact: ih.
  have : subseq (s0 :: t1) (merge r s1 (s0 :: t1)).
    by apply: ih => //; exact: path_le t0t1.
  by apply: subseq_trans; exact: subseq_cons.
rewrite /= eqxx.
rewrite [X in subseq _ X](_ : _ = merge r (s0 :: s1) t1)// IH//.
exact: path_sorted t0t1.
Qed.

Lemma merge_neq0 s t :
  (s != [::]) || (t != [::]) -> merge r s t != [::].
Proof.
elim: t s => [s|t0 t1 ih s].
  by rewrite eqxx orbF merge0r.
move=> /orP[|_].
  by move: s => [//|s0 s1 _ /=]; case: ifPn.
by move: s => [//|s0 s1/=]; case: ifPn.
Qed.

End merge_lemmas_eqType.

Definition disj_seq {T : eqType} (s t : seq T) :=
[disjoint [set` s] & [set` t]].

(* unlike subseq, disj_seq s t is true when s and t is disjoint as sets,
   not that each one be not a subseq of the other.
   i.e. disj_seq [:: a; a; b] [:: a; b; b] is false although
~ (subseq [:: a; a; b] [:: a; b; b] \/ subseq [:: a; b; b] [:: a; a; b]) is true *)
Example subseqNdisj_seq {T : eqType} :
let disj_seq' s t := ~~ (subseq s t || subseq t s) in
  forall a b : T, a == b = false ->
   let s := [:: a; a; b] in
   let t := [:: a; b; b] in
  disj_seq' s t /\ ~ disj_seq s t.
Proof.
move=> disj_seq' a b ab s t.
split.
- apply/norP; split.
  + by rewrite /= eqxx ?ifF ?ifF.
  + rewrite /= eqxx ifF; last by rewrite eq_sym.
    by rewrite eqxx.
- rewrite /disj_seq disj_set2E; apply/negP.
  apply/set0P.
  exists a => /=; split; exact: mem_head.
Qed.

Section disj_seq_lemmas.
Implicit Types (T : eqType) (R : realDomainType).

Lemma disj_seq_sym {T} (s t : seq T) :
  disj_seq s t = disj_seq t s.
Proof.
apply: eq_true_iff_eq.
suff tmp (p q : seq T) : disj_seq p q -> disj_seq q p by split; exact: tmp.
by move=> ?; rewrite /disj_seq disj_set_sym.
Qed.

Lemma disj_seq_allP {T} (s t : seq T) :
  disj_seq s t <-> all (fun x => x \notin s) t.
Proof.
split.
- move=> dsst.
  + apply/allP => x xt; apply/negP => xs.
    have := dsst.
    move/disj_set2P/eqP.
    apply/negP.
    apply/set0P.
    by exists x.
- move/allP=> ts.
  apply/disj_setPRL => x/= xt.
  apply/negP.
  exact: ts.
Qed.

Lemma disj_seq_filterr {T} (s t : seq T) (P : pred T) :
  disj_seq s t -> disj_seq s [seq x <- t | P x].
Proof.
move/disj_seq_allP => /allP st.
apply/disj_seq_allP; apply/allP => x; rewrite mem_filter.
by move=> /andP[_ xt]; exact: st.
Qed.

Lemma disj_seq_filterl {T} (s t : seq T) (P : pred T) :
  disj_seq s t -> disj_seq [seq x <- s | P x] t.
Proof.
by rewrite disj_seq_sym => ?; rewrite disj_seq_sym; exact: disj_seq_filterr.
Qed.

Lemma disj_seq_consr {T} (s t : seq T) (a : T) :
  disj_seq s (a :: t) -> disj_seq s t.
Proof.
move/disj_seq_allP => /allP st.
apply/disj_seq_allP; apply/allP => x memx.
by apply: st; rewrite in_cons memx orbT.
Qed.

Lemma disj_seq_consl {T} (s t : seq T) (a : T) :
  disj_seq (a :: s) t -> disj_seq s t.
Proof.
by rewrite disj_seq_sym => H; rewrite disj_seq_sym; exact: disj_seq_consr H.
Qed.

Lemma predCr_disj_seq {R} (s : seq R) (P : pred R) :
  disj_seq [seq x <- s | P x] [seq x <- s | predC P x].
Proof.
apply/disj_seq_allP/allP => x.
rewrite 2!mem_filter => /andP[/=/negP NPx xs].
by apply/nandP; left; apply/negP.
Qed.

Lemma predCl_disj_seq {R} (s : seq R) (P : pred R) :
  disj_seq [seq x <- s | predC P x] [seq x <- s | P x].
Proof. by rewrite disj_seq_sym; exact: predCr_disj_seq. Qed.

End disj_seq_lemmas.

Fixpoint merge_lt_seq {R : realDomainType} (l s : seq R) :=
  match s with
  | [::] => l
  | h :: s' =>
     [seq x <- l | x < h] ++ [:: h] ++ merge_lt_seq [seq x <- l | h < x] s'
  end.
(*
  transitive leT -> irreflexive leT -> forall [s : seq T], sorted leT s -> uniq s
lt_sorted_uniq_le:
  forall {disp : Order.disp_t} {T : porderType disp} (s : seq T),
  uniq s -> sorted <%O s = sorted <=%O s
*)

Lemma eq_mem_sub_mem {A} {a1 a2 : {pred A}} :
  (a1 =i a2) <-> {subset a1 <= a2} /\ {subset a2 <= a1}.
Proof.
split => [H | [H1 H2] a]; first by split=> a; rewrite H.
case/boolP: (a \in a2); [exact: H2 | apply: contraNF; exact: H1].
Qed.

Lemma merge_step {T} (leT : rel T) (a : T) (s : seq T) (b : T) (t : seq T) :
  merge leT (a :: s) (b :: t) =
     if leT a b then a :: merge leT s (b :: t) else b :: merge leT (a :: s) t.
Proof. by []. Qed.

Section order_merge_lt_seq_lemmas.
Context d {T : orderType d}.
Implicit Types (l s : seq T).

Lemma all_merge1r (s : seq T) (x : T) :
  all (fun z => x <= z)%O s -> merge <=%O s [:: x] = x :: s.
Proof.
elim: s => // a s IH.
rewrite merge_step/= => /andP[+ xs].
rewrite le_eqVlt => /predU1P[xa|xa].
  subst a; rewrite lexx IH//.
rewrite ifN//.
by rewrite -ltNge.
Qed.

Lemma merge_ltEle (s t : seq T) :
 sorted <=%O s -> sorted <=%O t ->
 merge <%O s t = merge <=%O s t.
Proof.
elim: s t => // a s IH t.
elim: t a s IH.
  by [].
move=> b t IHt a s IHs sorted_as sorted_bt.
rewrite 2!merge_step.
case: ifPn => [ab|].
  rewrite ifT; last exact: ltW.
  rewrite IHs//.
  exact: path_sorted sorted_as.
rewrite -leNgt => ba.
case: ifPn => [ab|_]; last first.
  rewrite IHt//.
  exact: path_sorted sorted_bt.
have {ab ba}eqab : a = b by apply/eqP; rewrite eq_le ab ba.
subst a.
rewrite IHt//; last exact: path_sorted sorted_bt.
rewrite merger_cons//; last exact: le_path_min.
rewrite merge_cons_mergel; last 2 first.
- exact: le_trans.
- exact: le_path_min.
rewrite all_merge1r//; last exact: le_path_min.
rewrite merger_cons//.
exact: le_path_min.
Qed.

End order_merge_lt_seq_lemmas.

Section merge_lt_seq_lemmas.
Context {R : realDomainType}.
Implicit Types (l s : seq R).

Lemma merge_lt_seq0r s : merge_lt_seq [::] s = s.
Proof.
elim: s => //= a s IH; by rewrite IH.
Qed.

Lemma merge_lt_seq_merge t s : sorted <%R t -> sorted <%R s ->
  disj_seq t s ->
  merge <%R t s = merge_lt_seq t s.
Proof.
elim: s t => //= a s.
- move=> _ _.
  by rewrite merge0r.
move=> IH t st pas dast.
rewrite -IH; last 3 first.
- exact: lt_sorted_filter.
- exact: path_sorted pas.
- apply: disj_seq_filterl.
  exact: disj_seq_consr dast.
elim: t st dast; first by [].
move=> b t IH' pbt dasbt /=.
case: ifPn => [ba|]; last rewrite -leNgt le_eqVlt => /predU1P[ab|ab].
- rewrite cat_cons; congr cons.
  rewrite ifN; last first.
    by rewrite -leNgt ltW.
  apply: IH'.
   exact: path_sorted pbt.
  exact: disj_seq_consl dasbt.
- have /disj_seq_allP/allP := dasbt.
  move/(_ a (mem_head a s)).
  rewrite in_cons; move/norP => [/negP].
  by rewrite ab.
- rewrite ab.
    have ->/= : [seq x <- t | x < a] = [::].
      apply/path_lt_filter0.
      apply: path_le ab pbt.
      exact: lt_trans.
    congr cons.
    rewrite path_lt_filterT; last first.
      apply: path_le ab pbt.
      exact: lt_trans.
  by elim: s IH pas IH' dasbt.
Qed.

Lemma sorted_filter_rcons y l : sorted <%R l ->
sorted <%R (rcons [seq x <- l | x < y] y).
Proof.
move=> sl; apply/(sortedP y)=> i; rewrite size_rcons ltnS => ily.
rewrite lt_sorted_ltn_nth ?inE ?size_rcons ?ltnS//; last by rewrite ltnW.
rewrite lt_sorted_pairwise pairwise_rcons.
apply/andP; split; first exact: filter_all.
by rewrite -lt_sorted_pairwise lt_sorted_filter.
Qed.

Lemma sorted_filter_path y l :
  sorted <%R l -> path <%R y [seq x <- l | y < x].
Proof.
move=> sl; rewrite lt_path_sortedE.
by apply/andP; split; last exact: lt_sorted_filter; exact: filter_all.
Qed.

Lemma sorted_merge_lt_seq l s :
  sorted <%R l -> sorted <%R s ->
  sorted <%R (merge_lt_seq l s).
Proof.
case: s => //= hs s sl ps.
rewrite sorted_cat_cons sorted_filter_rcons => //=.
elim: s hs l sl ps => /=.
  move=> ? ? ? ?; exact: sorted_filter_path.
move=> hs s IH hhs l sl /andP[hhshs ps].
rewrite cat_path; apply/andP; split.
  rewrite -filter_predI/=.
  under eq_filter do rewrite /= andbC.
  rewrite filter_predI.
  apply: sorted_filter_path.
  exact: lt_sorted_filter.
rewrite /=; apply/andP; split.
  move: (mem_last hhs [seq x <- [seq x <- l | hhs < x] | x < hs]).
  rewrite inE => /predU1P[->//|].
  by rewrite mem_filter => /andP[].
apply: IH => //.
exact: lt_sorted_filter.
Qed.

Lemma sorted_ltW d {T : orderType d} (s : seq T) :
  sorted <%O s -> sorted <=%O s.
Proof. by apply: sub_sorted; exact: ltW. Qed.

Lemma filterC_split (s t : seq R) :
  sorted <=%R s ->
  s = merge <=%R [seq x <- s | x \in t] [seq x <- s | x \notin t].
Proof.
move=> sorted_s.
apply: le_sorted_eq => //.
  by rewrite merge_sorted ?le_sorted_filter//; exact: le_total.
by rewrite perm_sym perm_merge perm_filterC.
Qed.

End merge_lt_seq_lemmas.

Section itv_partition_porder.
Context {d} {T : porderType d}.
Implicit Types (a b x : T) (s : seq T).

Lemma itv_partition_neq0 a b s : a != b -> itv_partition a b s -> s != [::].
Proof. by elim: s a b => // a' b' /negbTE a'b' []/=; rewrite a'b'. Qed.

Lemma itv_partition_sorted a b s : itv_partition a b s -> sorted <%O s.
Proof. by case => sa _; exact: path_sorted sa. Qed.

Lemma last_mem_itv_partition a b s :
  itv_partition a b s -> (a < b)%O -> b \in s.
Proof.
move: s; apply: last_ind => //.
- by move/itv_partition_nil ->; rewrite ltxx.
- move=> s' x' _ [_].
rewrite [a]lock.
  rewrite last_rcons => /eqP -> _.
  by rewrite mem_rcons mem_head.
Qed.

Lemma itv_partitionNnil a b s : (a < b)%O ->
 itv_partition a b s -> (0 < size s)%N.
Proof.
move=> ab p; apply: (@leq_trans (size [:: b])); rewrite ?size_subseq ?sub1seq//.
exact: last_mem_itv_partition ab.
Qed.

Lemma itv_partition_cons1 a b s x :
  s != [::] ->
  itv_partition a b (x :: s) -> itv_partition a b s.
Proof.
case: s => // s0 s1 _.
case => /= /and3P[ax xs0 s0s1 s0s1b]; split => //=.
by rewrite s0s1 andbT (lt_trans ax).
Qed.

(*Lemma itv_partition_head a b h s :
s != [::] ->
a < h < head b s -> itv_partition a b s ->
 itv_partition a b (h :: s).
Proof.
case: s => // s0 s1 _ /andP[ah hs0] /[dup]pabs [/=/andP[as0 pas] /eqP sb].
split; first by rewrite /=; apply/and3P; split => //.
by rewrite -sb.
Qed.*)

Let itv_partition_in_itv a b s :
  itv_partition a b s -> {in s, forall x, x \in `]a, b]}.
Proof.
move=> /[dup]parts.
move=> [/[dup]/lt_path_min/allP sa].
move=> /[dup]pas.
rewrite lt_path_pairwise.
move/pairwiseP => pwltas.
move/eqP => lsb.
move=> x xs.
rewrite in_itv/=; apply/andP; split; first exact: sa.
rewrite -lsb (last_nth a).
have xas : x \in a :: s by rewrite in_cons; apply/orP; right.
rewrite -(nth_index a xas).
rewrite le_eqVlt; apply/predU1P.
rewrite -implyNp => nlast.
apply: pwltas.
- rewrite inE/=.
  case: ifP => // _.
  by rewrite ltnS index_mem.
- by rewrite inE//.
- rewrite /=.
 move: s lsb parts sa pas x nlast xs xas.
  apply: last_ind => // s t IH.
  rewrite last_rcons => ->.
  move=> patsb asb psb x/[swap] xsb.
  rewrite nth_index; last first.
    by rewrite in_cons; apply/orP; right.
    move/[swap] => _.
    rewrite -last_nth last_rcons => xb.
  rewrite ifN; last first.
    by rewrite lt_eqF// asb.
  rewrite (_ : index x (rcons s b) = index x s); last first.
    rewrite -cats1 index_cat.
    rewrite ifT//.
    move: xsb.
    by rewrite mem_rcons in_cons => /predU1P; case.
  rewrite size_rcons ltnS.
  rewrite index_mem.
  move: xsb.
  rewrite mem_rcons in_cons.
  by move/predU1P; case.
Qed.

Lemma itv_partition_head_in_itv a b s t :
  itv_partition a b (rcons s t) -> {in s, forall x, x \in `]a, b[}.
Proof.
move=> pst x xs.
have in_ab := itv_partition_in_itv pst.
rewrite in_itv/=; apply/andP; split.
  have := in_ab x.
  rewrite mem_rcons in_cons.
  have H : (x == t) || (x \in s) by apply/orP; right.
  by move/(_ H); rewrite in_itv/= => /andP[ax xb].
have [] := pst.
rewrite lt_path_pairwise.
move/pairwiseP => lt_ast.
move/eqP <-; rewrite (last_nth a).
have : x \in a :: (rcons s t).
  rewrite in_cons; apply/orP; right.
  by rewrite mem_rcons in_cons xs orbT.
move/(nth_index a) <-.
apply: lt_ast; last 2 first.
- by rewrite inE.
- rewrite /=.
  rewrite ifF; last first.
    rewrite lt_eqF => //.
    have [/lt_path_min/allP + _] := pst.
    by apply; rewrite mem_rcons in_cons xs orbT.
  by rewrite size_rcons -cats1 index_cat xs ltnS index_mem.
rewrite inE index_mem.
rewrite in_cons; apply/orP; right.
by rewrite mem_rcons in_cons xs orbT.
Qed.

Lemma itv_partition_gt_lb a b s : (a < b)%O ->
  itv_partition a b s -> forall n, (a < nth b s n)%O.
Proof.
move=> ab ps n.
have [ns|ns] := ltnP n (size s).
  suff : nth b s n \in `]a, b].
    by rewrite in_itv/= => /andP[].
  apply: (itv_partition_in_itv ps).
  exact: mem_nth.
by rewrite nth_default.
Qed.

Lemma itv_partition_le_ub a b s :
  itv_partition a b s -> forall n, (nth b s n <= b)%O.
Proof.
move=> ps n.
have [ns|ns] := ltnP n (size s).
  suff : nth b s n \in `]a, b].
    by rewrite in_itv/= => /andP[].
  apply: (itv_partition_in_itv ps).
  exact: mem_nth.
by rewrite nth_default.
Qed.

Lemma itv_partition_lt_ub a b s :
  itv_partition a b s -> forall n, (n.+1 < size s)%N -> (nth b s n < b)%O.
Proof.
elim/last_ind : s => // s0 s1 _ ps n.
rewrite size_rcons ltnS => ns0.
pose s := rcons s0 s1.
rewrite -/s.
suff : nth b s n \in `]a, b[.
  by rewrite in_itv/= => /andP[].
apply: (@itv_partition_head_in_itv _ _ s0 s1) => //.
apply/(nthP b).
exists n => //.
by rewrite nth_rcons ns0.
Qed.

End itv_partition_porder.

Section merge_cats1.
Context {d} {R : orderType d}.
Variables (f : R -> R).
Implicit Types (s : seq R) (x : R).

Lemma merge_cats1 s t x : sorted <=%O s -> sorted <=%O (t ++ [:: x]) ->
  merge <=%O s (t ++ [:: x]) = merge <=%O (merge <=%O s t) [:: x].
Proof.
move=> ss st.
elim: s t x ss st.
  move=> t x ss st /=.
  rewrite sorted_merge//=; last exact: le_trans.
  by rewrite sorted_merge//; exact: le_trans.
move=> s0 s1 ih t.
move: t s0 s1 ih.
elim=> // t0 t1 ih' s0 s1 ih x ss stx.
rewrite /=.
rewrite -!/(merge <=%O (s0 :: s1) _).
have t0x : (t0 <= x)%O.
  move: stx.
  rewrite /sorted/=.
  move/le_path_min => /allP; apply.
  by rewrite mem_cat mem_head orbT.
have [s0t0|t0s0] := leP s0 t0.
  rewrite -/((t0 :: t1) ++ [:: x]).
  rewrite ih//; last exact: path_sorted ss.
  move: s0t0.
  rewrite le_eqVlt => /predU1P[s0t0|s0t0].
    subst t0.
    by rewrite merge_step// t0x.
  rewrite merge_step ifT//.
  apply: ltW.
  apply: lt_le_trans s0t0 t0x.
rewrite ih'//; last first.
  move: stx.
  apply: subseq_sorted; first exact: le_trans.
  rewrite [in X in subseq _ X]/=.
  by apply: subseq_cons.
rewrite [RHS]merger_cons//.
by rewrite /=andbT.
Qed.

End merge_cats1.

Section itv_partition_order.
Context {d} {T : orderType d}.
Implicit Types (a b x : T) (s : seq T).

Lemma sorted_merge1 h s : h \notin s ->
  sorted <%O s -> sorted <%O (merge <%O s [:: h]).
Proof.
elim: s h => // s0 s1 ih h hs /= s0s1.
have [s0h|s0h]/= := ltP s0 h.
  have s1h : sorted <%O (merge <%O s1 [:: h]).
    apply: ih (path_sorted s0s1).
    by apply: contra hs; rewrite inE orbC => ->.
  rewrite path_min_sorted//; apply/allP => x.
  rewrite mem_merge mem_cat => /orP[xs1|].
    by move/order_path_min : s0s1 => /(_ lt_trans)/allP/(_ _ xs1).
  by rewrite mem_seq1 => /eqP ->.
rewrite lt_neqAle s0h andbT.
by move: hs; rewrite !inE negb_or => /andP[->].
Qed.

Lemma notin_sorted_rcons s h :
  h \notin s -> sorted <%O s ->
  sorted <%O (rcons [seq x <- s | (x < h)%O] h).
Proof.
elim: s h => // s0 s1 ih h.
rewrite in_cons negb_or => /andP[hs0 hs1]/= s0s1.
have [s0h|] := ltP s0 h.
  have : sorted <%O s1 by exact: path_sorted s0s1.
  move/(ih _ hs1) => {}ih /=.
  rewrite path_min_sorted//; apply/allP => x.
  rewrite mem_rcons inE => /predU1P[->//|].
  rewrite mem_filter => /andP[xh xs1].
  move/order_path_min: s0s1 => /(_ lt_trans).
  by move/allP; exact.
rewrite le_eqVlt (negbTE hs0)/= => {}hs0.
rewrite path_lt_filter0//.
apply: path_le s0s1 => //.
exact: lt_trans.
Qed.

Lemma merge1E s h : h \notin s -> sorted <%O s ->
  merge <%O s [:: h] = itv_partitionL s h ++ itv_partitionR s h.
Proof.
move=> hs ss; apply: (@irr_sorted_eq _ <%O) => //.
- exact: lt_trans.
- exact: sorted_merge1.
- have sE := notin_itv_partition ss hs.
  rewrite /itv_partitionL -cats1 -catA/= sorted_cat_cons.
  rewrite notin_sorted_rcons//= path_min_sorted//.
    by apply: sorted_filter => //; exact: lt_trans.
  by apply/allP => x; rewrite mem_filter => /andP[].
- move=> i.
  rewrite mem_merge [in RHS]mem_cat mem_filter mem_rcons in_cons mem_filter.
  rewrite mem_cat mem_seq1.
  by have [//||] := ltgtP i h; rewrite ?(orbF,orbT).
Qed.

Lemma itv_partition_merge1 a b h s :
  (a < b)%O -> (a < h < b)%O -> h \notin s ->
  itv_partition a b s ->
  itv_partition a b (merge <%O s [:: h]).
Proof.
move=> ab /andP[ah hb] hs abs; rewrite merge1E//.
- apply: itv_partition_cat.
    exact: itv_partitionLP abs.
  exact: itv_partitionRP abs.
- exact: itv_partition_sorted abs.
Qed.

Lemma lt_sorted_rcons_notin s x : sorted <%O (rcons s x) -> x \notin s.
Proof.
elim: s x => // s0 [|s1 s2] ih x.
  by rewrite /= inE andbT => ?; rewrite gt_eqF.
rewrite [s1 :: s2]lock/= /= rcons_path => /andP[s0s1 s1x].
rewrite inE negb_or; apply/andP; split.
  rewrite gt_eqF//.
  move/order_path_min : s0s1 => /(_ lt_trans)/allP s0s1.
  rewrite (le_lt_trans _ s1x)//.
  apply/ltW.
  apply/s0s1.
  by rewrite -lock/= mem_last.
rewrite -lock.
apply: ih.
rewrite -lock in s0s1 s1x.
apply: (@path_sorted _ _ s0). (* TODO: path_sorted implicits *)
by rewrite rcons_path s1x s0s1.
Qed.

(*Lemma sorted_itv_partition_merge a b s t :
  (a < b)%O ->
  sorted <%O t ->
  (forall x, x \in t -> x \in `]a, b[) ->
  itv_partition a b s ->
  itv_partition a b (merge <%O s t).
Proof.
elim/last_ind: t s a b.
  move=> s a b ab _ _.
  by rewrite merge0r.
move=> t0 t1 ih s a b ab sorted_t ts abs.
rewrite -cats1.
rewrite (@merge_cats1 _ _ s t0 t1); last 2 first.
  exact: (itv_partition_sorted abs).
  by rewrite cats1.
apply: itv_partition_merge1 => //.
  apply ts.
  by rewrite mem_rcons mem_head.
rewrite mem_merge mem_cat negb_or; apply/andP; split.
  apply ts.
  by rewrite mem_rcons mem_head.
  by apply: sorted_rcons sorted_t.
apply: ih => //.
move: sorted_t.
rewrite -cats1.
by move/cat_sorted2 => -[].
move=> x xt0.
apply: ts.
by rewrite mem_rcons inE xt0 orbT.
Qed.*)

Lemma sorted_itv_partition_merge a b s t :
  (a < b)%O ->
  sorted <%O t ->
  (forall x, x \in t -> (x \in `]a, b[) /\ (x \notin s)) ->
  itv_partition a b s ->
  itv_partition a b (merge <%O s t).
Proof.
elim/last_ind: t s a b.
  move=> s a b ab _ _.
  by rewrite merge0r.
move=> t0 t1 ih s a b ab sorted_t ts abs.
rewrite -cats1.
rewrite merge_ltEle; last 2 first.
- apply: sorted_ltW.
  by have[/path_sorted] := abs.
- by rewrite cats1 sorted_ltW.
rewrite (@merge_cats1 _ _ s t0 t1); last 2 first.
- by apply: sorted_ltW; exact: (itv_partition_sorted abs).
- by rewrite cats1 sorted_ltW.
rewrite -merge_ltEle//; last first.
- apply: merge_sorted; rewrite ?sorted_ltW//.
      exact: le_total.
    by have [/path_sorted] := abs.
  rewrite sorted_rconsE in sorted_t; last exact: lt_trans.
  by have/andP[] := sorted_t.
apply: itv_partition_merge1 => //.
  apply ts.
  by rewrite mem_rcons mem_head.
rewrite mem_merge mem_cat negb_or; apply/andP; split.
  apply ts.
  by rewrite mem_rcons mem_head.
  by apply: lt_sorted_rcons_notin sorted_t.
rewrite -merge_ltEle; last 2 first.
    by have [/path_ltW/path_sorted] := abs.
  rewrite sorted_rconsE in sorted_t; last exact: lt_trans.
  by have/andP[/sorted_ltW] := sorted_t.
apply: ih => //.
move: sorted_t.
rewrite -cats1.
by move/cat_sorted2 => -[].
move=> x xt0.
apply: ts.
by rewrite mem_rcons inE xt0 orbT.
Qed.

Lemma itv_partition_inbetween_notin a b s : itv_partition a b s ->
  forall x k, (k < size s)%N ->
  x \in `]nth b (a :: s) k, nth b (a :: s) k.+1[ ->
  x \notin s.
Proof.
elim: s a b => // s0 s1 ih a b abs0s1 x [_/=|k].
  rewrite in_itv/= => /andP[ax xs0].
  rewrite inE negb_or; apply/andP; split.
    apply/negP => /eqP s0x.
    by rewrite s0x ltxx in xs0.
  apply/negP => xs1.
  case: abs0s1 => /= /andP[as0].
  move/lt_path_min => /allP/(_ x).
  rewrite xs1 => /(_ isT).
  by rewrite ltNge (ltW xs0).
rewrite /= ltnS => ks1.
rewrite in_itv/= => /andP[kx xk].
rewrite inE negb_or; apply/andP; split.
  apply/negP => /eqP s0x.
  case: abs0s1 => /= /andP[as0].
  move: k kx ks1 xk => [|k kx ks1 xk].
    by rewrite /= s0x ltxx.
  move/lt_path_min => /allP/(_ (nth b (s0 :: s1) k.+1)).
  have : nth b (s0 :: s1) k.+1 \in s1.
    apply/(nthP b); exists k => //=.
    by rewrite (leq_trans _ ks1).
  move=> /[swap] /[apply] /=.
  rewrite -s0x.
  by rewrite ltNge (ltW kx).
have : itv_partition s0 b s1.
  by case: abs0s1 => /= => /andP[as0 s0s1 s1b].
move/ih => /(_ _ _ ks1); apply.
by rewrite in_itv/= kx xk.
Qed.

Lemma itv_partition_notin_inbetween a b s x : itv_partition a b s ->
  x \notin s -> (a < x < b)%O ->
  exists2 k, (k < size s)%N &
  x \in `]nth b (a :: s) k, nth b (a :: s) k.+1[.
Proof.
elim: s a b x => [a b x|s0 s1 ih a b x].
  case => /= _ /eqP <-{b} _ /andP[/lt_trans] /[apply].
  by rewrite ltxx.
move=> abs.
rewrite !inE negb_or => /andP[].
rewrite neq_lt => /orP[|] xs0 xs1 /andP[ax xb].
  exists 0 => //=.
  by rewrite in_itv/= ax xs0.
have s0bs1 := itv_partition_cons abs.
have := ih _ _ _ s0bs1 xs1.
rewrite xs0 xb => /(_ isT)[k ks1 memx].
by exists k.+1.
Qed.

Lemma lt_merge_min s x : all (<%O x) s -> merge <%O s [:: x] = x :: s.
Proof.
case: s => // s0 s1 /= /andP[xs0 xs1].
by rewrite ltNge (ltW xs0)/=.
Qed.

Lemma lt_merge1_max s x : all (<%O ^~ x) s ->
   merge <%O s [:: x] = rcons s x.
Proof.
elim: s x => // s0 s1 /= ih x s0s1.
destruct s1 as [|s1 s2].
  by move/andP: s0s1 => [-> _].
have [gt_s0|le_s0] := ltP s0 _.
  rewrite ih//.
  by have/andP[] := s0s1.
have/andP[] := s0s1.
by rewrite ltNge le_s0.
Qed.

End itv_partition_order.

Section variation_lemmas.
Context {R : realDomainType}.
Implicit Types (a b : R) (f : R -> R).

Lemma variation_behead a b s f :
  variation (nth b s 0) b f (behead s) <= variation a b f s.
Proof.
case: s => [|s0 s1]/=.
  by rewrite !variation_nil.
by rewrite /variation/= big_nat_recl//= lerDr.
Qed.

Lemma variation_nth a b f s : a < b ->
  itv_partition a b s ->
  forall k, (k.+2 <= size s)%N ->
  variation a (nth b s k) f (itv_partitionL s (nth b s k)) <= variation a b f s.
Proof.
move=> ab abs k ks.
rewrite [in leRHS](@in_itv_partition _ _ (nth b s k) s); last 2 first.
  exact: itv_partition_sorted abs.
  apply/(nthP b).
  exists k => //.
  by rewrite (leq_trans _ ks).
rewrite (@variation_cat _ (nth b s k))//.
- by rewrite lerDl variation_ge0.
- apply/ltW.
  exact: (itv_partition_gt_lb _ abs).
- apply: (@itv_partition_nth_le _ _ a _ _ k.+1) => //.
  by rewrite (leq_trans ks).
- apply: itv_partitionLP (abs).
    exact: itv_partition_gt_lb.
  exact: (itv_partition_lt_ub abs).
- apply: itv_partitionRP (abs).
    exact: itv_partition_gt_lb.
  exact: (itv_partition_lt_ub abs).
Qed.

Lemma filter_iota a b s : a < b ->
  itv_partition a b s ->
  forall k, (k < size s)%N ->
  [seq x <- s | x < nth b s k] = take k s.
Proof.
elim: s a b => //= s0 s1 ih a b ab abs [_|k].
  rewrite /= ltxx.
  rewrite -(filter_pred0 s1).
  apply: eq_in_filter => r s1r.
  apply/negbTE/negP => rs0.
  case: abs => /= /andP[as0] + _.
  move/order_path_min => /(_ lt_trans)/allP => /(_ _ s1r).
  rewrite ltNge.
  by rewrite (ltW rs0).
rewrite ltnS => ks1.
rewrite /=.
rewrite ifT; last first.
  case: abs => /= /andP[as0].
  move/order_path_min => /(_ lt_trans)/allP + _; apply.
  apply/(nthP b).
  by exists k.
rewrite (ih s0)//=.
have /= := @itv_partition_lt_ub _ _ _ _ _ abs O.
apply.
by rewrite ltnS (leq_trans _ ks1).
by case: abs => /= /andP[as0 s0s1 s0s1b].
Qed.

Lemma variation_nth_nth a b f s : a < b ->
  itv_partition a b s ->
  forall k, (k.+2 < size s)%N ->
  variation a (nth b s k) f (itv_partitionL s (nth b s k)) <=
  variation a (nth b s k.+1) f (itv_partitionL s (nth b s k.+1)).
Proof.
move=> ab abs k ks.
have H : nth b s k < nth b s k.+1.
  case: abs => sa /eqP asb.
  move/pathP : sa => /(_ b) /(_ k.+1) /=.
  apply.
  by rewrite (leq_trans _ ks).
have H1 : itv_partitionL s (nth b s k.+1) =
    rcons (itv_partitionL s (nth b s k)) (nth b s k.+1).
  rewrite /itv_partitionL.
  rewrite -!cats1.
  congr cat.
  rewrite (@filter_iota a)//; last first.
    by rewrite (leq_trans _ ks).
  rewrite (@filter_iota a)//; last first.
    by rewrite (leq_trans _ ks)// ltnW.
  rewrite (take_nth b) -?cats1//.
  by rewrite (leq_trans _ ks)// ltnW.
rewrite H1.
rewrite -cats1.
rewrite (@variation_cat _ (nth b s k))//; last 4 first.
  apply/ltW.
  by apply: (itv_partition_gt_lb _ abs).
  by apply/ltW.
  apply: itv_partitionLP (abs).
  by apply: itv_partition_gt_lb => //.
  apply: (itv_partition_lt_ub abs) => //.
  by rewrite (leq_trans _ ks).
  rewrite /itv_partition/=.
  split => //.
  by rewrite H.
by rewrite lerDl// variation_ge0.
Qed.

Lemma variationxx a b f s :
  variation a b f (a :: s) = variation a b f s.
Proof. by rewrite /variation/= big_nat_recl//= subrr normr0 add0r. Qed.

Lemma variation_stutter a b f x s :
  variation a b f [:: x, x & s] = variation a b f (x :: s).
Proof.
rewrite /variation.
rewrite [x :: s]lock /= big_nat_recl// -lock.
by rewrite /= !big_nat_recl//= subrr normr0 add0r.
Qed.

Lemma variation_recl a b f x s :
  variation a b f (x :: s) = `|f x - f a| + variation x b f s.
Proof. by rewrite /variation/= big_nat_recl. Qed.

Lemma variation_recr a b f s :
  variation a b f (rcons s (last a s)) = variation a b f s.
Proof.
rewrite {1}/variation/=.
rewrite size_rcons.
rewrite big_nat_recr//=.
rewrite [X in _ + X](_ : _ = 0) ?addr0; last first.
  rewrite nth_rcons ltnn eqxx.
  rewrite -/(rcons (a :: s) (last a s)).
  rewrite nth_rcons/= ltnS leqnn/=.
  by rewrite -last_nth subrr normr0.
rewrite /variation.
rewrite big_seq [RHS]big_seq.
apply: eq_bigr => /= k.
rewrite mem_index_iota leq0n/= => ks.
rewrite nth_rcons ks.
congr (`| _ - f _ |).
rewrite -/(rcons (a :: s) (last a s)).
by rewrite nth_rcons/= ltnS (ltnW ks).
Qed.

Lemma in_variation_merge1 a b f s x : a < b -> itv_partition a b s ->
  x \in s ->
  variation a b f (merge <%O s [:: x]) = variation a b f s.
Proof.
elim: s x a b => // s0 s1 ih x a b ab abs.
have s0bs1 := itv_partition_cons abs.
rewrite inE => /predU1P[->{x}|xs1].
  by rewrite /= ltxx variation_stutter.
rewrite /=.
have [s0x|s0x] := ltP s0 x.
  rewrite variation_recl.
  rewrite ih//; last first.
    apply: itv_partition_size_neq0 s0bs1.
    move: xs1.
    rewrite -index_mem.
    exact: leq_trans.
  by rewrite variation_recl.
case: abs => /= /andP[as0 s0s1 _].
move/order_path_min : s0s1 => /(_ lt_trans)/allP/(_ _ xs1).
by rewrite ltNge s0x.
Qed.

Lemma sorted_undup_merge_subseq (s t : seq R) :
  sorted <=%R s -> sorted <%R t ->
  subseq s t -> undup (merge <%R t s) = t.
Proof.
move=> ss st subseq_st.
have lest : sorted <=%R t by exact: sorted_ltW.
apply: (le_sorted_eq _ lest).
  apply: undup_sorted; first exact: le_trans.
  rewrite merge_ltEle//.
  apply: merge_sorted => //; first exact: le_total.
rewrite -{2}(@undup_id _ t); last first.
  by have := st; rewrite lt_sorted_uniq_le => /andP[].
apply: perm_undup.
move=> x.
rewrite mem_merge mem_cat.
apply: orb_idr.
exact: mem_subseq.
Qed.

Lemma le_sorted_merge_sym (s t : seq R) :
  sorted <=%R s -> sorted <=%R t -> merge <=%R s t = merge <=%R t s.
Proof.
elim: s t.
  by move=> t; rewrite merge0r.
move=> a s IHs t.
elim: t a s IHs => // b t IHt a s IHs sas sbt.
rewrite 2!merge_step.
case: ifPn => [|]; last rewrite -ltNge; first rewrite le_eqVlt => /predU1P[|].
- move=> ?; subst a.
  rewrite lexx.
  rewrite IHs//; last exact: path_sorted sas.
  rewrite merger_cons; last exact: le_path_min.
  rewrite -IHt//; last exact: path_sorted sbt.
  rewrite merger_cons; last exact: le_path_min.
  rewrite IHs//.
    exact: path_sorted sas.
  exact: path_sorted sbt.
- move=> ab.
  rewrite ifN; last by rewrite -ltNge.
  rewrite IHs//.
  exact: path_sorted sas.
- move=> ba.
  rewrite ifT ?ltW//.
  rewrite IHt//.
  exact: path_sorted sbt.
Qed.

(* generalize *)
Lemma le_sorted_mergeA (r s t : seq R) :
   sorted <=%R r -> sorted <=%R s -> sorted <=%R t ->
   merge <%R r (merge <%R s t) =
   merge <%R (merge <%R r s) t.
Proof.
move=> sr ss st.
rewrite !merge_ltEle//; last 2 first.
- by rewrite merge_sorted//; exact: le_total.
- by rewrite merge_sorted//; exact: le_total.
by rewrite mergeA//; first exact: le_total; exact: le_trans.
Qed.

Lemma lt_sorted_mem_filter_exchange (s t : seq R) :
  sorted <%R s -> sorted <%R t ->
  [seq x <- s | x \in t] = [seq x <- t | x \in s].
Proof.
move=> ss st; apply: lt_sorted_eq; rewrite ?lt_sorted_filter//.
by move=> ?; rewrite 2!mem_filter andbC.
Qed.

Lemma merge_filter_undup (s t : seq R) :
sorted <%R s -> sorted <%R t ->
let t' := [seq x <- t | x \notin s] in
merge <%R s t' = undup (merge <%R s t).
Proof.
move=> sorted_s sorted_t t'.
set t0 := [seq x <- t | x \in s].
have less : sorted <=%R s by exact: sorted_ltW.
have lest : sorted <=%R t by exact: sorted_ltW.
have -> : merge <%R s t = merge <%R (merge <%R s t') t0.
  rewrite (filterC_split s lest).
  rewrite merge_ltEle//; last by rewrite -filterC_split.
  rewrite [X in merge _ _ X]le_sorted_merge_sym ?le_sorted_filter//.
  rewrite -merge_ltEle//; last first.
    by rewrite le_sorted_merge_sym ?le_sorted_filter// -filterC_split.
  rewrite -merge_ltEle// ?le_sorted_filter//.
  by rewrite le_sorted_mergeA// ?le_sorted_filter.
rewrite sorted_undup_merge_subseq//.
- exact: le_sorted_filter.
- rewrite merge_lt_seq_merge//; last 2 first.
  + exact: lt_sorted_filter.
  + by apply/disj_seq_allP/allP => x; rewrite mem_filter => /andP[].
  apply: sorted_merge_lt_seq => //.
  exact: lt_sorted_filter.
apply: (@subseq_trans _ s); last exact: subseq_mergel.
rewrite /t0 lt_sorted_mem_filter_exchange//.
exact: filter_subseq.
Qed.

End variation_lemmas.

(* if the new point falls into the interval between x_k and x_{k+1}, the
  increase in the sum V due to this point is not greater than twice the
  oscillation w_k of the function f(x) on the segment [x_k, x_{k+1}] *)
Section twice.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).
Implicit Types (s : seq R) (x : R).

Lemma itvcc_max_sup a b f : a <= b ->
  {within `[a, b], continuous f} ->
  forall c, c \in `[a, b] ->
   (f c = sup (f @` `[a, b]) <-> (forall x, x \in `[a, b] -> f x <= f c)).
Proof.
move=> ab cf c cab; split => H.
- have [d dab dmax] := EVT_max ab cf.
  move=> x /dmax.
  move/le_trans; apply.
  rewrite H.
  apply: ub_le_sup; last by exists d.
  exists (f d) => _/=[y yab <-].
  exact: dmax.
- apply/eqP; rewrite eq_le; apply/andP; split.
    apply: ub_le_sup => //.
    by exists (f c) => _/=[? ? <-]; exact: H.
  apply: ge_sup; first by exists (f c).
  move=> _/=[? ? <-]; exact: H.
Qed.

Lemma itvcc_min_inf a b f : a <= b ->
  {within `[a, b], continuous f} ->
  forall c, c \in `[a, b] ->
   (f c = inf (f @` `[a, b]) <-> (forall x, x \in `[a, b] -> f c <= f x)).
Proof.
Abort.

Lemma continuous_oscillationE (a b : R) (f : R -> R) :
a < b ->
{within `[a, b], continuous f} ->
exists s : R * R,
  [/\ s.1 != s.2,
  s.1 \in `[a, b], s.2 \in `[a, b],
  (forall t, t \in `[a, b] -> f s.2 <= f t <= f s.1) &
  `|f s.1 - f s.2|%:E = oscillation f `[a, b]].
Proof.
move=> ab cf.
have [d' dab maxd] := EVT_max (ltW ab) cf.
have [e' eab mine] := EVT_min (ltW ab) cf.
have fcst : (f d' = f e') = {in `[a, b], f =1 cst (f a)}.
  apply/propext; split.
  - move=> fdfe x xab.
    apply/eqP; rewrite eq_le; apply/andP; split.
      apply: (le_trans (maxd x xab)).
      rewrite fdfe; apply: mine.
      by rewrite boundl_in_itv bnd_simp/= ltW.
    apply: (le_trans _ (mine x xab)).
    rewrite -fdfe; apply: maxd.
    by rewrite boundl_in_itv bnd_simp/= ltW.
  by move=> H; rewrite H//; apply/esym; rewrite H.
(*
pose e := if f d' == f e' then (a + 2 * b) / 3 else e'.
pose d := if f d' == f e' then (2 * a + b) / 3 else d'.
*)
pose e := if f d' == f e' then a else e'.
pose d := if f d' == f e' then b else d'.

have neq_ed : d != e.
  rewrite /e/d; case: ifPn => [_|H].
    by rewrite neq_lt; apply/orP; right.
(* by right; rewrite ltr_pM2r// 2!mulr_natl 2!mulr2n -addrA [ltRHS]addrCA ltrD2r. *)
  apply/negP; move/eqP => ed.
  have := fcst.
  rewrite propeqE => -[_ /contra_not]; apply.
    exact/eqP.
  by rewrite -fcst ed.
exists (d, e); split => //=.
- move: dab; rewrite in_itv/= => /andP[ae eb].
  by rewrite /d in_itv/=; apply/andP; split; case: ifP => //; rewrite ltW.
- move: eab; rewrite in_itv/= => /andP[ae eb].
  by rewrite /e in_itv/=; apply/andP; split; case: ifP => //; rewrite ltW.
- move=> t tab.
  apply/andP; split; rewrite /d/e; case: ifP => [|_].
  + move/eqP; rewrite fcst => H.
    rewrite H; last by rewrite boundl_in_itv/= bnd_simp ltW.
    by rewrite [leRHS]H.
  + exact: mine.
  + move/eqP; rewrite fcst => H.
    rewrite [leRHS]H; last by rewrite boundr_in_itv/= bnd_simp ltW.
    by rewrite H.
  + exact: maxd.
- rewrite /oscillation ifN; last first.
  by apply/neitvP => /=; rewrite bnd_simp ltW.
- 
Abort.

Lemma oscillation_set1 a f : oscillation f [set a] = 0.
Proof.
rewrite /oscillation ifF; last first.
  by apply/negP/negP/set0P; exists a.
by rewrite !image_set1 ereal_sup1 ereal_inf1 subee.
Qed.

Lemma variation_oscillation a b c1 c2 f :
  {within `[a, b], continuous f} -> c1 \in `[a, b] -> c2 \in `[a, b] ->
  (`|f c1 - f c2|%:E <= oscillation f `[a, b])%E.
(*   ereal_sup [set (EFin \o f) x | x in `[a, b]] -
   ereal_inf [set (EFin \o f) x | x in `[a, b]])%E.
*)
Proof.
have [ab|] := ltP a b; last first.
 rewrite le_eqVlt => /predU1P[-> cf|ba _].
   rewrite !in_itv/= -!eq_le => /eqP <- /eqP <-.
   by rewrite set_itvE oscillation_set1 subrr normr0.
  rewrite in_itv/= => /andP[/le_trans] /[apply].
  by rewrite leNgt ba.
move=> cf c1ab c2ab.
rewrite /oscillation.
have [d dab maxd] := EVT_max (ltW ab) cf.
have [e eab mine] := EVT_min (ltW ab) cf.
rewrite (@le_trans _ _ (f d - f e)%:E)//.
  have [fac|fca] := leP (f c2) (f c1).
    rewrite ger0_norm ?subr_ge0// lee_fin.
    by rewrite lerB// ?maxd ?mine// ?in_itv/= ?lexx ?(ltW ac) ?(ltW cb)// (ltW (lt_trans ac cb)).
  rewrite ltr0_norm ?subr_lt0// lee_fin opprB lerB//.
    by rewrite maxd.
  by rewrite mine.
rewrite ifN; last first.
  by apply/neitvP; rewrite bnd_simp ltW.
rewrite EFinB leeB//.
  apply: le_ereal_sup_tmp.
  by exists (f d)%:E => //=; exists d.
by apply: ge_ereal_inf; exists (f e)%:E => //=; exists e.
Qed.

Lemma variation_merge1_oscillation a b f s : a < b ->
  {within `[a, b], continuous f} ->
  itv_partition a b s ->
  forall x, x \in `]a, b[ -> x \notin s ->
  forall k, (k < (size s))%N ->
    x \in `]nth b (a :: s) k, nth b (a :: s) k.+1[ ->
  ((variation a b f (merge <%R s [:: x]))%:E <=
   (variation a b f s)%:E +
   2 * oscillation f `[nth b (a :: s) k, nth b (a :: s) k.+1])%E.
Proof.
move=> ab cf abs x xab xs k ks xk.
set s' := merge _ _ _.
apply: (@le_trans _ _ (variation a b f
    (itv_partitionL s' x ++ itv_partitionR s' x))%:E).
  rewrite lee_fin.
  apply: variation_itv_partitionLR.
  by move: xab; rewrite in_itv/= => /andP[].
  by move: xab; rewrite in_itv/= => /andP[].
  exact: itv_partition_merge1.
rewrite (@variation_cat _ x); last 4 first.
  by move: xab; rewrite in_itv/= => /andP[/ltW].
  by move: xab; rewrite in_itv/= => /andP[_ /ltW].
  apply: (@itv_partitionLP _ _ _ b).
  by move: xab; rewrite in_itv/= => /andP[].
  by move: xab; rewrite in_itv/= => /andP[].
  exact: itv_partition_merge1.
  apply: (@itv_partitionRP _ _ a).
  by move: xab; rewrite in_itv/= => /andP[].
  by move: xab; rewrite in_itv/= => /andP[].
  exact: itv_partition_merge1.
have s'E : s' = itv_partitionL s x ++ itv_partitionR s x.
  rewrite /s' merge1E//.
  exact: itv_partition_sorted abs.
set x_k := nth b (a :: s) k.
set x_k1 := nth b (a :: s) k.+1.
have axk : a <= x_k.
  rewrite /x_k.
  destruct k as [|k]; first by [].
  rewrite /=.
  exact/ltW/itv_partition_gt_lb.
have xkx : x_k <= x.
  move: xk.
  rewrite -/x_k.
  by rewrite in_itv/= => /andP[/ltW].
have sa : itv_partitionL s a = [:: a].
  rewrite /itv_partitionL.
  rewrite [X in rcons X _](_ : _ = [::])//.
  rewrite -(filter_pred0 s).
  apply: eq_in_filter => r rs.
  apply/negbTE.
  rewrite -leNgt.
  move/(nthP b) : rs => -[m ms <-{r}].
  apply/ltW.
  by apply/itv_partition_gt_lb.
have K1 : [seq x0 <- itv_partitionR s x | x0 < x] = [::].
  rewrite /itv_partitionR.
  rewrite -filter_predI.
  rewrite -(filter_pred0 s).
  apply: eq_in_filter => r rs/=.
  apply/negbTE/negP => /andP[/lt_trans/[apply]].
  by rewrite ltxx.
move: xk; rewrite -/x_k -/x_k1 in_itv/= => /andP[{}xkx xxk1].
have H1 : variation a x f (itv_partitionL s' x) =
    variation a x_k f (itv_partitionL s x_k)
    + variation x_k x f [:: x].
  destruct k as [|k].
    rewrite /x_k/=.
    rewrite sa.
    rewrite {2}/variation/= big_nat1/= subrr normr0 add0r.
    rename xkx into xa.
    rename xxk1 into xs0.
    have s'x : itv_partitionL s' x = [:: x].
      rewrite /itv_partitionL.
      rewrite [X in rcons X](_ : _ = [::])//.
      rewrite s'E.
      rewrite filter_cat.
    have H1 : [seq x0 <- itv_partitionL s x | x0 < x] = [::].
      rewrite filter_rcons ltxx filter_id.
      case: abs.
      destruct s as [|s0 s1].
        rewrite /= => _ /eqP.
        move: ab => /[swap] ->.
        by rewrite ltxx.
      rewrite [X in X -> _ -> _]/= => /andP[as0].
      move/order_path_min => /(_ lt_trans)/allP s1s0 /eqP ?.
      rewrite -(filter_pred0 (s0 :: s1)).
      rewrite /= in xs0.
      apply: eq_in_filter => r/=.
      rewrite inE => /predU1P[rs0|].
        apply/negbTE/negP => rx.
        rewrite rs0 in rx.
        by rewrite ltNge (ltW xs0) in rx.
      move/s1s0 => s0r.
      apply/negbTE/negP => rx.
      have := lt_trans s0r rx.
      by rewrite ltNge (ltW xs0).
    rewrite H1.
    by rewrite K1.
    by rewrite s'x.
  rewrite -variation_cat; last 4 first.
  by [].
  exact/ltW.
  apply: (@itv_partitionLP _ _ _ b) => //.
    rewrite /x_k /=.
    by apply/itv_partition_gt_lb.
  move: xab; rewrite in_itv/= => /andP[_].
  by apply: le_lt_trans; exact/ltW.
  rewrite /itv_partition/=.
  by rewrite xkx.
  rewrite s'E.
  congr variation.
  rewrite /itv_partitionL.
  rewrite filter_cat rcons_cat filter_rcons ltxx filter_id.
  rewrite -cats1.
  rewrite catA.
  congr cat.
  rewrite K1 cats0.
  rewrite [in LHS](@in_itv_partition _ _ x_k _ (itv_partition_sorted abs)); last first.
    apply/(nthP b).
    rewrite /x_k.
    exists k => //.
    by rewrite (leq_trans _ ks).
  rewrite filter_cat.
  rewrite /itv_partitionL.
  rewrite filter_rcons.
  rewrite xkx.
  have H1 : [seq x0 <- itv_partitionR s x_k | x0 < x] = [::].
    rewrite /itv_partitionR.
    rewrite -filter_predI.
    rewrite -(filter_pred0 s).
    apply: eq_in_filter => r rs/=.
    apply/negbTE/negP => /andP[rx xkr].
    move: rs.
    apply/negP.
    apply: (@itv_partition_inbetween_notin _ _ _ _ _ abs _ k.+1) => //.
    by rewrite -/x_k -/x_k1 in_itv/= xkr/= (lt_le_trans rx)//= ltW.
  rewrite H1 cats0.
  rewrite -filter_predI.
  congr rcons.
  apply: eq_in_filter => r rs/=.
  by rewrite andb_idl// => /lt_trans; exact.
have K2 : [seq x0 <- itv_partitionL s x | x < x0] = [::].
  rewrite /itv_partitionL.
  rewrite filter_rcons ltxx -filter_predI.
  rewrite -(filter_pred0 s).
  apply: eq_in_filter => r sr/=.
  apply/negbTE/negP => /andP[/lt_trans] /[apply].
  by rewrite ltxx.
have H2 : variation x b f (itv_partitionR s' x) =
  variation x x_k1 f [:: x_k1]
  + variation x_k1 b f (itv_partitionR s x_k1).
  rewrite -variation_cat; last 4 first.
    exact: ltW.
    by apply: (itv_partition_le_ub abs).
    rewrite /itv_partition/=.
    by rewrite xxk1.
    move: ks.
    rewrite leq_eqVlt => /predU1P[k1s|k1s].
      have xk1b : x_k1 = b.
        rewrite /x_k1 k1s.
        rewrite nth_last/=.
        by case: abs => _ /eqP.
      have sxk1 : itv_partitionR s x_k1 = [::].
        rewrite -(filter_pred0 s) /itv_partitionR.
        rewrite xk1b.
        apply: eq_in_filter => r rs.
        apply/negbTE.
        rewrite -leNgt.
        move/(nthP b) : rs => [m ms <-].
        by apply: (itv_partition_le_ub abs).
      by rewrite sxk1 /itv_partition xk1b/=.
    apply: (@itv_partitionRP _ _ a) => //.
      by rewrite (le_lt_trans axk)// (lt_trans xkx).
    rewrite /x_k1.
    destruct s as [|s0 s1] => //.
    rewrite (@lt_le_trans _ _ (nth b [:: a, s0 & s1] k.+2))//.
      case: abs => /pathP /[swap]/eqP asb.
      by apply => //.
    by move/itv_partition_le_ub : abs => /(_ k.+1)/=.
  congr variation.
  rewrite s'E.
  rewrite [LHS]filter_cat.
  rewrite K2/= /itv_partitionR filter_id.
  rewrite [in LHS](@in_itv_partition _ _ x_k1 _ (itv_partition_sorted abs)); last first.
    by apply/(nthP b); exists k.
  rewrite filter_cat.
  have -> : [seq x0 <- itv_partitionL s x_k1 | x < x0] = [:: x_k1].
    rewrite /itv_partitionL.
    rewrite filter_rcons xxk1 -filter_predI.
    rewrite -cats1.
    suff : [seq x0 <- s | predI [eta > x] (<%R^~ x_k1) x0] = [::] by move=> ->.
    rewrite -(filter_pred0 s).
    apply: eq_in_filter => r sr/=.
    apply/negbTE/negP => /andP[xr rxk1].
    move: sr.
    apply/negP.
    apply: (@itv_partition_inbetween_notin _ _ _ _ _ abs _ k) => //.
    by rewrite -/x_k -/x_k1 in_itv/= rxk1 (lt_trans xkx xr).
  rewrite /=; congr cons.
  rewrite /itv_partitionR.
  rewrite -filter_predI.
  apply: eq_in_filter => r sr/=.
  rewrite andb_idl// => xk1r.
  exact: (lt_trans _ xk1r).
rewrite H1 H2.
rewrite (addrC (variation x x_k1 _ _)).
rewrite addrACA.
rewrite EFinD.
rewrite leeD//.
  destruct k as [|k].
    rewrite {1}/variation.
    have -> : itv_partitionL s x_k = [:: a].
      rewrite /itv_partitionL -cats1 /x_k/=.
      rewrite [X in X ++ _](_ : _ = [::])//.
      rewrite -(filter_pred0 s).
      apply: eq_in_filter => r sr.
      apply/negbTE; rewrite -leNgt.
      move/(nthP b) : sr => [m ms mr].
      rewrite -mr.
      apply/ltW.
      by apply/itv_partition_gt_lb.
    rewrite big_nat1/= subrr normr0 add0r.
    rewrite lee_fin.
    have -> : itv_partitionR s x_k1 = behead s.
      destruct s as [|s0 s1] => //=.
      rewrite /x_k1/= ltxx.
      rewrite /itv_partitionR.
      rewrite -[RHS](filter_predT s1).
      apply: eq_in_filter => r rs1.
      case: abs => /= /andP[as0].
      move=> /order_path_min => /(_ lt_trans) + _ => /allP.
      by apply.
    rewrite /x_k1 /=.
    exact: variation_behead.
  move: ks.
  rewrite leq_eqVlt => /predU1P[k1s|k1s].
    (* copipe *) have xk1b : x_k1 = b.
      rewrite /x_k1 k1s.
      rewrite nth_last/=.
      by case: abs => _ /eqP.
    (* copipe *) have sxk1 : itv_partitionR s x_k1 = [::].
      rewrite -(filter_pred0 s) /itv_partitionR.
      rewrite xk1b.
      apply: eq_in_filter => r rs.
      apply/negbTE.
      rewrite -leNgt.
      move/(nthP b) : rs => [m ms <-].
      by apply: (itv_partition_le_ub abs).
    rewrite sxk1.
    rewrite variation_nil addr0.
    rewrite lee_fin.
    rewrite /x_k/=.
    rewrite variation_nth//.
    by rewrite -k1s.
  rewrite lee_fin.
  rewrite [in leRHS](@in_itv_partition _ _ x_k1 _ (itv_partition_sorted abs)); last first.
    apply/(nthP b).
    exists k.+1 => //.
    by rewrite (leq_trans _ k1s).
  rewrite (@variation_cat _ x_k1)//; last 4 first.
    by rewrite (le_trans axk)// (le_trans (ltW xkx))// ltW.
    rewrite /x_k1.
    rewrite /=.
    exact: (@itv_partition_le_ub _ _ a).
    apply: itv_partitionLP (abs) => //.
    rewrite /x_k1/=.
    exact: itv_partition_gt_lb => //.
    rewrite /x_k1/=.
    exact: (itv_partition_lt_ub abs).
    apply: itv_partitionRP (abs) => //.
    rewrite /x_k1/=.
    exact: itv_partition_gt_lb.
    rewrite /x_k1/=.
    exact: (itv_partition_lt_ub abs).
  by rewrite lerD2r /x_k /x_k1/= variation_nth_nth.
rewrite mule_natl.
rewrite mule2n.
rewrite EFinD.
rewrite leeD//.
  rewrite /variation/= big_nat_recr//= big_nil add0r.
  apply: (@variation_oscillation _ _ _ _ f).
  apply: continuous_subspaceW cf.
  apply: subset_itv; rewrite bnd_simp//.
  by apply: (itv_partition_le_ub abs).
  by rewrite in_itv/= (ltW xkx) (ltW xxk1).
  by rewrite in_itv/= lexx (ltW (lt_trans xkx _)).
rewrite /variation/= big_nat_recr//= big_nil add0r.
apply: (@variation_oscillation _ _ _ _ f).
apply: continuous_subspaceW cf.
apply: subset_itv; rewrite bnd_simp//.
by apply: (itv_partition_le_ub abs).
rewrite in_itv/= lexx ltW//.
by rewrite (lt_trans xkx).
by rewrite in_itv/= (ltW xkx) (ltW xxk1).
Qed.

End twice.

Section omega_max.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).
Implicit Types (s : seq R) (x : R).

Definition omega_max a b f s : \bar R :=
   \big[maxe/-oo%E]_(0 <= n < size s) oscillation f
    `[(nth b (a :: s)) n, (nth b (a :: s)) n.+1].

(*
Lemma bigmaxE T Q FH :
forall (F : T -> R) (HF : forall x, 0 <= F x),
  (\big[max/0%:nng]_(i in Q) (FH i)%:nng)%:num = (\big[max/0]_(i in Q) (F i)).

   reflect (\big[maxr/0%:nng]_(0 <= k < n) (P k)%:nng)%:num)
   (\big[maxr/0%R]_(0 <= k < n) P k).
*)

Lemma omega_max_nil a b f : omega_max a b f [::] = -oo%E.
Proof. by rewrite /omega_max /= big_nil. Qed.

Lemma omega_max_ge0 a b f s : s != [::] -> (0 <= omega_max a b f s)%E.
Proof.
case: s => [//|h t s0].
by rewrite /omega_max/= big_nat_recl//= le_max oscillation_ge0.
Qed.

Lemma omega_max_le_oscillation a b f s :
  itv_partition a b s ->
  (omega_max a b f s <= oscillation f `[a, b])%E.
Proof.
move=> ps.
rewrite /omega_max big_seq bigmax_le//.
  by rewrite leNye.
move=> /= n.
rewrite mem_iota add0n subn0 leq0n/= => ns.
apply: oscillation_sub.
apply: subset_itvScc; rewrite bnd_simp//.
  by apply: itv_partition_nth_ge => //; rewrite ltnS ltnW.
exact: (itv_partition_le_ub ps).
Qed.

Lemma omega_max_cons a b f s x :
  a <= x <= head a s ->
  s != [::] ->
  (omega_max a b f (x :: s) <= omega_max a b f s)%E.
Proof.
elim: s => // h s' IH /=/andP[ax xh] _.
rewrite /omega_max/=.
rewrite 3?big_nat_recl//=.
rewrite maxA.
apply: le_max2 => //.
rewrite maxEge; case: ifPn => _; apply: oscillation_sub.
  by apply: subset_itvl; rewrite bnd_simp.
by apply: subset_itvr; rewrite bnd_simp.
Qed.

Lemma le_omega_max a b f s t :
  s != [::] ->
  path <=%R a s ->
  sorted <=%R t ->
  subseq s t ->
  (omega_max a b f t <= omega_max a b f s)%E.
Proof.
elim: t a s.
  by move=> ? ?; rewrite omega_max_nil leNye.
move=> ht t IHt a s s0.
elim: s t s0 IHt => // hs s IHs t _ IHt /= /andP[ahs phss] phtt.
case: ifPn.
  move/eqP => hsht qst.
  case: s IHs phss qst => [|h s IHs phss qst].
(*
    rewrite hsht.
    rewrite /omega_max/=.
    rewrite big_nat1/= big_nat_recl/=.
    apply: bigmax_le.
*)
  admit.
  rewrite /omega_max/=.
  rewrite 2?big_nat_recl//= hsht.
  rewrite le_max2 => //.
  (* apply: IHt => //. *)
    admit.
  (* rewrite le_max; apply/orP. *)
    admit.
Abort.
(*
rewrite /=; case: ifPn => hshht /andP[ahs] phss.
  move=> /andP[hhtht phtt] sub_stt.
  apply: (@le_trans _ _ (omega_max a b f [:: ht & t])).
    apply: omega_max_cons => //=.
    rewrite hhtht andbT.
    by have /eqP <- := hshht.
  have := (IHs s).
  have := @omega_max_cons a b f s hs.
  have /eqP <- := hshht; rewrite ahs/=.
  have := (IHs s).
  by rewrite /= eqxx IH.

rewrite /=; case: ifPn => [/eqP|] at0.
  move: rat0; rewrite -{}at0 {t0} => raa.
  rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
  exact: (subseq_trans (subseq_cons _ _) (ih s IH)).
rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
exact: ih.

  rewrite /=; case: ifPn => hsht phss.
  move=> sub_stt.
  have := @omega_max_cons a b f t ht.
  have := (IHs s).
  by rewrite /= eqxx IH.
rewrite /=; case: ifPn => [/eqP|] at0.
  move: rat0; rewrite -{}at0 {t0} => raa.
  rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
  exact: (subseq_trans (subseq_cons _ _) (ih s IH)).
rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
exact: ih.

elim: t s.
  by move => ? /negP.
move=> x t' IHs s; move/IHs => IHs'.
elim: s IHs' => //.
Admitted.
*)

Import Order.Def.

Lemma omega_max_merge1 a b f s x :
  s != [::] -> path <=%R a s -> last a s == b ->
  a <= x <= b ->
(omega_max a b f (merge <%R s [:: x]) <= omega_max a b f s)%E.
Proof.
move: s a.
elim => // h s IH a _ pahs lsb.
case: s IH pahs lsb => [_|].
  rewrite /= andbT => /[swap]/eqP -> ab.
  move=> /andP[ax xb].
  rewrite ifN; last by rewrite -leNgt.
  rewrite /omega_max/=.
  rewrite !big_nat_recl//= !big_nil/=.
  rewrite 2!maxeNy.
  rewrite ge_max; apply/andP; split; apply: oscillation_sub.
  - exact: subset_itvl.
  - exact: subset_itvr.
move=> s0 s1 IH.
rewrite [s0 :: s1]lock => /=/andP[ah phs] ls1b /andP[ax xb].
case: ifPn => [hx|].
  rewrite /omega_max/=.
  rewrite !big_nat_recl//=.
  rewrite le_max2//.
  rewrite -lock IH//=.
  - by move: phs; rewrite -lock.
  - by move: ls1b; rewrite -lock.
  - by rewrite xb ltW.
rewrite -leNgt => xh.
rewrite /omega_max/=.
rewrite !big_nat_recl//=.
rewrite maxA le_max2// ge_max; apply/andP; split; apply: oscillation_sub.
- exact: subset_itvl.
- exact: subset_itvr.
Qed.

End omega_max.

Section nonnegR_is_monoid.
Context {R : realType}.

Notation maxr := (@maxr {nonneg R}).

Lemma maxrA : associative maxr.
Proof. exact: maxA. Qed.

Lemma maxr0 : left_id 0%:nng maxr.
Proof.
move=> x.
apply/max_idPr.
rewrite (_ : widen_itv 0%:itv = widen_itv `|@GRing.zero R|%:itv).
  by rewrite num_abs_le.
apply/esym/eqP.
by rewrite num_abs_eq0.
Qed.

Lemma max0r : right_id 0%:nng maxr.
Proof.
move=> x.
apply/max_idPl.
rewrite (_ : widen_itv 0%:itv = widen_itv `|@GRing.zero R|%:itv).
  by rewrite num_abs_le.
apply/esym/eqP.
by rewrite num_abs_eq0.
Qed.

HB.instance Definition _ := Monoid.isLaw.Build {nonneg R} 0%:nng maxr maxrA maxr0 max0r.

End nonnegR_is_monoid.

Section itv_partition_length_lemmas.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).
Implicit Types (s : seq R) (x : R).

Definition mesh a b s : R := let pnth := nth b (a :: s) in
  (\big[maxr/0%:nng]_(0 <= n < size s) `|pnth n.+1 - pnth n|%:nng)%:num.

Lemma mesh_ge0 a b s : 0 <= mesh a b s.
Proof. by rewrite /mesh. Qed.

Lemma mesh_eq_merge_subseq a b s t :
  path <=%R a s -> path <=%R a t ->
  subseq t s ->
  mesh a b (merge <=%R s t) = mesh a b s.
Proof.
elim: t s => //=.
  move=> pas _ _.
  by rewrite merge0r.
move=> h t IH s pas /andP[ah pht] subhts.
rewrite merge_cons_mergel; last 2 first.
- exact: le_trans.
- exact: le_path_min.
rewrite IH; last 3 first.
- apply: merge_path => //.
  by rewrite /= ah.
- apply: (path_le _ ah) => //; exact: le_trans.
- apply: (@subseq_trans _ s); last exact: subseq_mergel.
  apply: subseq_trans subhts.
  exact: subseq_cons.
rewrite /mesh.
rewrite size_merge.
have hs : h \in s.
  have /mem_subseq/subsetP := subhts.
(*  move/(_ h); rewrite 2!inE; apply.
  exact: mem_head.
set n := index h (s ++ [:: h]).
have : (n <= size (s ++ [:: h]))%N.
  by rewrite index_size.
rewrite size_cat/= addn1 => ns.*)
(* needs Monoid instance! *)
(* have : (\big[@Num.max {nonneg R}/_]_(0 <= n0 < (size s).+1)
      widen_itv `|nth b (merge <=%R s [:: h]) n0 - nth b (a :: merge <=%R s [:: h]) n0|%:itv)%:num = a.
rewrite big_cat_nat.
have := (@big_cat_nat {nonneg R} (0%:nng) (@maxr {nonneg R})). (leq0n n) ns).
*)
Abort.

Lemma path_merge_ltW a b (s t : seq R) :
  path <=%R a s -> subseq t s ->
  mesh a b s = mesh a b (merge <=%R s t).
Proof.
Abort.

Lemma mesh_merge1_le a b s x :
  path <%R a s -> a <= x <= b -> last a s == b ->
  mesh a b (merge <%R s [:: x]) <= mesh a b s.
Proof.
move=> ps /eqP sb.
have [xs|xs] := boolP (x \in s).
  (* rewrite itv_partition_max_merge_subseq. *)
  admit.
(*
apply: subseq_itv_partition_max.
have itv_partition_max_merge :
*)
Abort.

Lemma mesh_merge1' a b l s x :
  path <=%R a s -> last a s == b ->
  mesh a b s <= l ->
  mesh a b (merge <=%R s [:: x]) <= l.
Proof.
elim: s => //.
  move=> ? /=.
  rewrite /mesh/=.
  rewrite big_nat_recl// big_nil/=.
rewrite /mesh /=.
Abort.

Lemma mesh_merge a b l s t :
  mesh a b s <= l ->
  mesh a b (merge <=%R s t) <= l.
Proof.
Abort.

End itv_partition_length_lemmas.

Section lt_merge_lemmas.
Context {R : realType}.
Implicit Types (s t r : seq R) (x : R).

Local Notation sorted := (@sorted R <%R).
Local Notation path := (@path R <%R).
Local Notation merge := (@merge R <%R).

Definition udmerge s t := (undup (merge s t)).

Let lt_pathNmem x s : path x s -> x \in s = false.
Proof.
move/lt_path_min/allP => ltxs.
apply/negP => xs.
have := ltxs x xs.
by rewrite ltxx.
Qed.

Lemma merge_cons s t x :
  path x t -> merge s (x :: t) = merge (merge s [:: x]) t.
Proof.
move=> xt.
elim: s x t xt => [x t xt|s0 s1 ih x t xt].
  by rewrite /= merger_cons// order_path_min//; exact: lt_trans.
rewrite /=.
rewrite -/(merge (s0 :: s1) t).
case: ifPn => [s0x|].
  rewrite merger_cons//; last first.
    rewrite order_path_min//.
      exact: lt_trans.
    apply: path_le xt => //.
    exact: lt_trans.
  by rewrite ih.
rewrite -leNgt => xs0.
case: t xt xs0 => [//|t0 t1 xt xs0].
rewrite /=.
rewrite -/(merge (s0 :: s1) t1).
rewrite -/(merge (x :: s0 :: s1) t1).
case: ifPn => [s0t0|].
  by rewrite (le_lt_trans xs0).
rewrite -leNgt => t0s0.
by move: xt => /= /andP[->].
Qed.

End lt_merge_lemmas.

Section itv_partition_udmerge_disj_seq_lemmas.
Context {R : realType}.
Implicit Types (a b : R) (s : seq R) (x : R).

Lemma itv_partition_merge a b s t :
 itv_partition a b s ->
 itv_partition a b t ->
 disj_seq s t -> itv_partition a b (merge <%R s t).
Proof.
move=> ps pt.
(*move=> /disj_seq_allP[/allP ts /allP st].*)
Abort.

Lemma itv_partition_udmerge a b s t :
 itv_partition a b s ->
 itv_partition a b t ->
 itv_partition a b (udmerge s t).
Proof.
Abort.

End itv_partition_udmerge_disj_seq_lemmas.

(* NB: available as PR https://github.com/math-comp/analysis/pull/1809 *)
Lemma compact_unif_continuousP {R : realType} (a b : R) f :
  {within `[a, b], continuous f} <-> @unif_continuous (subspace `[a, b]) R f.
Proof.
Admitted.

Section variation_merge_omega_max.
Context {R : realType}.
Variables (a b : R) (f : R -> R).
Hypothesis (ab : a < b).
Hypothesis cf : {within `[a, b], continuous f}.
Implicit Types (s : seq R) (x : R).

Lemma variation_merge1_omega_max s : itv_partition a b s ->
  forall x, x \in `[a, b] ->
    ((variation a b f (merge <%R s [:: x]))%:E <=
       (variation a b f s)%:E + 2 * omega_max a b f s)%E.
Proof.
move=> abs.
case: (abs) => pas lsb x.
have [xs|xs] := boolP (x \in s).
  move=> _.
  rewrite in_variation_merge1// leeDl// mule_ge0// omega_max_ge0//.
  rewrite -size_eq0 -lt0n.
  by move: xs; rewrite -index_mem; exact: leq_trans.
rewrite in_itv/= => /andP[].
rewrite le_eqVlt => /predU1P[ax|ax].
  rewrite le_eqVlt => /predU1P[xb|xb].
    by move: ab; rewrite ax xb ltxx.
  subst x.
  rewrite lt_merge_min; last first.
   by move/order_path_min : pas => /(_ lt_trans).
   rewrite variationxx leeDl// mule_ge0// omega_max_ge0//.
   destruct s => //.
   move/eqP : lsb xb => /= ->.
   by rewrite ltxx.
rewrite le_eqVlt => /predU1P[xb|xb].
  subst x.
  have bs := last_mem_itv_partition abs ab.
  by move/negP in xs.
have := @variation_merge1_oscillation R a b f s ab cf abs x.
rewrite in_itv/= ax xb => /(_ isT xs).
have := @itv_partition_notin_inbetween _ _ a b s x abs xs.
rewrite ax xb => /(_ isT)[k ks xk].
move/(_ k ks xk)/le_trans; apply.
rewrite leeD2l//.
rewrite lee_pmul ?oscillation_ge0//.
rewrite /omega_max.
pose h := fun k => oscillation f `[(nth b (a :: s) k), (nth b s k)].
apply: (le_bigmax_seq -oo%E k xpredT h) => //.
by rewrite mem_index_iota ks.
Qed.

End variation_merge_omega_max.

Section variation_merge_tmp.
Context {R : realType}.
Variables (a b : R) (f : R -> R).
Hypothesis (ab : a < b).
Hypothesis cf : {within `[a, b], continuous f}.
Implicit Types (s : seq R) (x : R).

Lemma variation_merge_tmp l s t :
  itv_partition a b s -> mesh a b s <= l ->
  itv_partition a b t ->
  disj_seq s t ->
  ((variation a b f (merge <%R s t))%:E <= (variation a b f s)%:E +
  (size t)%:R%:E * 2 * omega_max a b f s)%E.
Proof.
have [->|] := pselect (omega_max a b f s = +oo%E).
  move=> _ _ _ _.
  rewrite -muleA mulry/= gtr0_sg// mul1e.
  case: t => /=.
    rewrite merge0r mul0e adde0//.
  move=> ht t.
  rewrite mulry gtr0_sg ?mul1e//.
  rewrite addey//.
  exact: leey.
move/eqP; rewrite -ltey => maxoo.
elim: t s maxoo.
  move=> s _ _.
  by rewrite merge0r 2!mul0e adde0.
move=> h t IH s maxoo ps sl pht disjst.
have s0 : s != [::].
    apply: itv_partition_neq0 ps.
    by move: ab; rewrite lt_neqAle => /andP[].
rewrite merge_cons; last first.
  have [+ _] := pht.
  by rewrite /= => /andP[].
move: t s maxoo ps sl s0 IH pht disjst; apply: last_ind.
  move=> s maxoo ps sl s0 IH pht disjst.
  rewrite merge0r/= mul1e.
  apply: variation_merge1_omega_max => //.
  case: pht => /= /andP[ah _ /eqP ->].
  by rewrite bound_itvE ltW.
move=> t tt IH1 s maxoo ps sl s0 IH2 pht disjst.
have ttb : tt = b.
  move: pht => [_].
  by rewrite last_cons last_rcons => /eqP.
apply: (le_trans (IH2 _ _ _ _ _ _)).
- apply: le_lt_trans maxoo.
  have [ps_lt lsb] := ps.
  apply: omega_max_merge1 => //.
  exact: path_ltW.
- have [] := ps.
  move/path_ltW => psle lasb.
  apply/andP; split.
  + by have [/=/andP[/ltW+ _] _] := pht.
  + rewrite -(@nth_index _ b h (h :: (rcons t tt))); last exact: mem_head.
    apply: itv_partition_nth_le; first by rewrite /= eqxx//.
    exact: itv_partition_cons pht.
- apply: itv_partition_merge1 => //.
  + admit.
  + admit.
(*- apply: (le_trans (itv_partition_max_merge1_le _ _ _)) => //.
  + by have [] := ps.
  + admit.
  + by have [] := ps.
(*
rewrite disj_seq_merge_ltW; last first.
    apply/disj_seq_allP; split; apply/allP.
      admit.
    admit.
  exact: itv_partition_max_merge1'.
*)
- apply: (itv_partition_cons1 _ pht).
  have pt := itv_partition_cons pht.
  apply: (itv_partition_neq0 _ pt).
  rewrite lt_eqF//.
  rewrite -rcons_cons in pht.
  have [+ _] := pht.
  rewrite -rev_path.
  move/order_path_min.
  have lt_trans_rev : transitive (fun x => <%R ^~ x).
    admit.
  move/(_ lt_trans_rev).
  move/allP.
  rewrite last_rcons ttb.
  apply.
  by rewrite mem_rev belast_rcons in_cons; apply/orP; right; exact: mem_head.
  (* have := (itv_partition_head_in_itv pht). *)
- admit.
have hab : h \in `]a, b[.
  admit.
(*
rewrite -(natr1 (size t)) (EFinD (size t)%:R).
rewrite 2?muleDl ?mul1e => //; last first.
  admit.
rewrite addeA.
apply: (@le_trans _ _ ((variation a b f (merge <%R s [:: h]))%:E +
  ((size t)%:R)%:E * 2 * omega_max a b f s)%E).
  rewrite leeD2l//.
  rewrite lee_pmul//.
    apply: omega_max_ge0.
    - by apply: merge_neq0; rewrite orbT.
    - exact: ltW.
    - apply: path_merge.
        by move: hab; rewrite in_itv/= => /andP[].
      by case: ps.
  apply: omega_max_merge1 => //.
  - apply: path_ltW.
    by have [] := ps.
  - admit.
  - admit.
rewrite -addeAC leeD2r//.
apply: variation_merge1 => //.
have /disj_seq_allP[/allP + _] := disjst.
apply.
exact: mem_head.
*) *)
Abort.

End variation_merge_tmp.

Section bigmax.
Context {R : realType}.
Local Open Scope ereal_scope.

Lemma le_bigmax_seq2 (r s : seq nat) (F F' : nat -> \bar R) :
  (forall i, i \in r -> exists2 j, j \in s & F i <= F' j) ->
  \big[maxe/-oo]_(i <- r) F i <= \big[maxe/-oo]_(i <- s) F' i.
Proof.
elim: r s F F' => [s F F' _|/= r0 r1 ih s F F' h].
  by rewrite big_nil// leNye.
rewrite big_cons ge_max; apply/andP; split.
  have := h r0.
  rewrite mem_head => /(_ isT)[j js] /le_trans; apply.
  by apply: le_bigmax_seq.
apply: ih => i ir1.
have := h i.
by rewrite inE ir1 orbT => /(_ isT).
Qed.

End bigmax.

Section variation_merge.
Context {R : realType}.
Implicit Type (f : R -> R).
Implicit Types (s : seq R) (x : R).

Lemma itv_partition_mergeS a b s t : (a < b)%R ->
  itv_partition a b s ->
  sorted <%R t ->
  (forall x, x \in t -> (x \in `]a, b[) /\ x \notin s) ->
  forall i, (i < size (merge <%R s t))%N ->
  exists2 j, (j < size s)%N &
  `[(nth b (a :: merge <%R s t) i), (nth b (merge <%R s t) i)]
  `<=`
  `[(nth b (a :: s) j), (nth b s j)].
Proof.
elim : t s a b => [s a b ab abs _ abt i|t0 t1 ih].
  rewrite /= merge0r => si.
  by exists i.
move=> s.
elim: s t0 t1 ih => //=.
  move=> t0 t1 ih a b ab /itv_partition_nil.
  move: ab => /[swap] ->.
  by rewrite ltxx.
move=> s0 s1 ih' t0 t1 ih a b ab.
rewrite -/(merge <%R (s0 :: s1)).
move=> abs t0t1 abt [_|i].
  exists O => //=.
  have [s0t0|t0s0] := ltP s0 t0.
    apply: subset_itvl.
    by rewrite bnd_simp.
  apply: subset_itvl.
  by rewrite bnd_simp.
have [s0t0|t0s0] := ltP s0 t0.
  have : s0 <= b.
    case: abs => /= /andP[as0 s0s1 /eqP <-].
    by apply: path_lt_le_last.
  rewrite le_eqVlt => /predU1P[?|s0b].
    subst s0.
    destruct s1; last first.
      clear ih' ih.
      case: abs.
      rewrite [in X in X -> _]/= ab.
      rewrite [in X in _ -> X -> _]/=.
      rewrite andTb => /andP[bs ss1] /eqP ss1b.
      move/order_path_min : ss1 => /(_ lt_trans)/allP H.
      exfalso.
      destruct s1.
        simpl in ss1b.
        subst s.
        by rewrite ltxx in bs.
      simpl in ss1b.
      move: bs.
      rewrite ltNge => /negP; apply.
      rewrite -ss1b ltW// H//.
      by rewrite mem_last.
    simpl.
    rewrite ltnS => it1.
    exists O => //=.
    apply/subset_itv; rewrite bnd_simp//=.
      case: i it1 => /= [|i] it1.
        exact: ltW.
      rewrite (le_trans (ltW ab))//.
      case: i it1 => /= [|i] it1.
        exact: ltW.
      rewrite (le_trans (ltW s0t0))//.
      move/order_path_min : t0t1 => /(_ lt_trans)/allP H.
      apply/ltW/H.
      apply/nthP.
      exists i => //.
      rewrite ltnS in it1.
      by rewrite (leq_trans _ it1)//.
    clear ih' ih.
    have : nth b (t0 :: t1) i \in t0 :: t1.
      apply/(nthP b).
      by exists i.
    move/abt => [+ _].
    by rewrite in_itv/= => /andP[_ /ltW].
  rewrite /= ltnS => ist.
  have s0bs1 := itv_partition_cons abs.
  have : exists2 j : nat,
     (j < size s1)%N &
     `[(nth b (s0 :: merge <%R s1 (t0 :: t1)) i),
     (nth b (merge <%R s1 (t0 :: t1)) i)]
     `<=` `[(nth b (s0 :: s1) j), (nth b s1 j)].
    apply: ih' => //.
    move=> x.
    rewrite inE => /predU1P[->{x}|].
      split.
        rewrite in_itv/= s0t0/=.
        have := abt t0.
        rewrite mem_head => /(_ isT).
        by rewrite in_itv/= => -[/andP[]].
      have := abt t0.
      rewrite mem_head => /(_ isT)[_].
      by rewrite inE negb_or => -/andP[].
    move=> xt1.
    rewrite !in_itv/=.
    split.
      apply/andP; split.
        rewrite (lt_trans s0t0)//.
        move: t0t1.
        move/order_path_min => /(_ lt_trans)/allP.
        by apply.
      have := abt x.
      rewrite inE xt1 orbT => /(_ isT).
      by rewrite in_itv/= => -[/andP[]].
    have := abt x.
    rewrite inE xt1 orbT => /(_ isT)[_].
    by rewrite inE negb_or => /andP[].
  case => j Hj H1.
  exists j.+1.
    by rewrite ltnS.
  by rewrite /=.
rewrite /=.
rewrite ltnS => ist.
have : s0 <= b.
  case: abs => /= /andP[as0 s0s1 /eqP <-].
  by apply: path_lt_le_last.
rewrite le_eqVlt => /predU1P[?|s0b].
  subst s0.
  destruct s1; last first.
    (* copipe *)
    clear ih'.
    clear ih.
    case: abs.
    rewrite [in X in X -> _]/= ab.
    rewrite [in X in _ -> X -> _]/=.
    rewrite andTb => /andP[bs ss1] /eqP ss1b.
    move/order_path_min : ss1 => /(_ lt_trans)/allP H.
    exfalso.
    destruct s1.
      simpl in ss1b.
      subst s.
      by rewrite ltxx in bs.
    simpl in ss1b.
    move: bs.
    rewrite ltNge => /negP; apply.
    rewrite -ss1b ltW// H//.
    by rewrite mem_last.
  simpl.
  exists O => //= x /=.
  rewrite !in_itv/= => /andP[ix xi].
  apply/andP; split.
    rewrite {ix xi}(le_trans _ ix)//.
    case: i ist => [|i] ist//=.
      have := abt t0.
      rewrite mem_head => /(_ isT).
      by rewrite in_itv/= => -[]/andP[/ltW].
    clear ih ih'.
    have : nth b (merge <%R [:: b] t1) i \in b :: t1.
      rewrite -[X in _ \in X]cat1s.
      rewrite -(mem_merge <%R).
      apply/(nthP b).
      exists i => //.
      by rewrite (leq_trans _ ist)//.
    rewrite inE => /predU1P[->|h].
      exact/ltW.
    have := abt (nth b (merge <%R [:: b] t1) i).
    rewrite inE h orbT => /(_ isT)[].
    by rewrite in_itv/= => /andP[/ltW].
  rewrite (le_trans xi)//.
  have : nth b (merge <%R [:: b] t1) i \in b :: t1.
    rewrite -[X in _ \in X]cat1s.
    rewrite -(mem_merge <%R).
    apply/(nthP b).
    by exists i => //.
  rewrite inE => /predU1P[->//|h].
  have := abt (nth b (merge <%R [:: b] t1) i).
  rewrite inE h orbT => /(_ isT)[].
  by rewrite in_itv/= => /andP[_ /ltW].
have sorted_t1 : sorted <%R t1.
  by apply: path_sorted t0t1.
have Htmp : (forall x, x \in t1 -> (x \in `]a, b[) /\ x \notin (s0 :: s1)).
  move=> x xt2.
  apply: abt.
  by rewrite inE xt2 orbC.
have [j Hj Hj']:= ih _ _ _ ab abs sorted_t1 Htmp _ ist.
exists j => //=.
apply: subset_trans Hj' => //.
apply: subset_itvr.
rewrite bnd_simp/=.
destruct i => /=.
  have := abt t0.
  rewrite mem_head => /(_ isT).
  by rewrite in_itv/= => -[/andP[]/ltW].
done.
Qed.

Lemma itv_partition_sorted_rcons a b s (t0 : seq R) (t : R) :
  a < b -> itv_partition a b s ->
  sorted <%R (rcons t0 t) ->
  (forall x, x \in rcons t0 t -> (x \in `]a, b[) /\ x \notin s) ->
  exists2 k : nat,
    (k.+1 < size (a :: merge <%R s t0))%N &
    t \in `](nth b (a :: merge <%R s t0) k),
    (nth b (a :: merge <%R s t0) k.+1)[.
Proof.
move=> ab abs sorted_t0t xnotin.
have H0 : itv_partition a b (merge <%R s t0).
  apply: sorted_itv_partition_merge => //.
    move: sorted_t0t.
    by rewrite -cats1 => /cat_sorted2[].
  move=> x xt0.
  have := xnotin x.
  by rewrite mem_rcons inE xt0 orbT => /(_ isT).
have H1 : t \notin merge <%R s t0.
  rewrite mem_merge mem_cat negb_or; apply/andP; split.
    by apply xnotin; rewrite mem_rcons mem_head.
  have := @sorted_uniq_in _ <%R (rcons t0 t).
  rewrite rcons_uniq.
  move=> /(_ _ _ sorted_t0t)/andP[||//].
    move=> ? ? ? ? ? ?.
    exact: lt_trans.
  move=> ? ?.
  by rewrite ltxx.
have H2 : a < t < b.
  have := xnotin t.
  rewrite mem_rcons inE eqxx/= => /(_ isT).
  by rewrite in_itv/= => -[].
have [k K1 K2] := @itv_partition_notin_inbetween _ R a b (merge <%R s t0) t H0 H1 H2.
by exists k.
Qed.

(* without disj_seq *)
Lemma variation_merge_notin f a b (ab : a < b) s t :
  {within `[a, b], continuous f} ->
  itv_partition a b s ->
  sorted <%R t ->
  (forall x, x \in t -> (x \in `]a, b[) /\ x \notin s) ->
  ((variation a b f (merge <%R s t))%:E <= (variation a b f s)%:E +
  (size t)%:R%:E * 2 * omega_max a b f s)%E.
Proof.
elim/last_ind : t a b ab s.
  move=> a b ab s cf abs _ _.
  rewrite /= !mul0e adde0.
  rewrite merge0r.
  done.
move=> t0 t1 ih a b ab s cf abs st tabs.
have le_sorted_s: sorted <=%R s.
  by have [/path_ltW/path_sorted] := abs.
have le_sorted_t0: sorted <=%R t0.
  rewrite lt_sorted_rconsE in st.
  by have /andP[/sorted_ltW] := st.
rewrite -cats1.
rewrite merge_ltEle//; last by rewrite cats1 sorted_ltW.
rewrite merge_cats1//; last by rewrite cats1 sorted_ltW.
have [k ks t1k] : exists2 k,
   (k.+1 < size ((a :: merge <%R s t0)))%N &
     t1 \in `](nth b (a :: merge <%R s t0) k),
     (nth b (a :: merge <%R s t0) k.+1)[.
  clear ih.
  exact: itv_partition_sorted_rcons.
rewrite -merge_ltEle//; last first.
  by rewrite merge_sorted//; exact: le_total.
apply: le_trans.
  apply: (@variation_merge1_oscillation _ _ _ _ _ _ _ _ _ _ _ k) => //.
  - rewrite -merge_ltEle//.
    apply: sorted_itv_partition_merge => //.
      by move: st; rewrite -cats1 => /cat_sorted2[].
    move=> x xt0.
    apply: tabs.
    by rewrite mem_rcons inE xt0 orbT.
  - have := tabs t1.
    by rewrite mem_rcons inE eqxx/= => /(_ isT)[].
  - rewrite mem_merge mem_cat negb_or; apply/andP; split.
      apply tabs.
      by rewrite mem_rcons mem_head.
    exact: lt_sorted_rcons_notin.
  - by rewrite -merge_ltEle.
  - by rewrite -merge_ltEle.
(*  rewrite (leq_trans ks)//=. size_merge size_cat leq_addr.*)
apply: (@le_trans _ _ (
  (variation a b f s)%:E + ((size t0)%:R)%:E * 2 * omega_max a b f s
  +
  2 * oscillation f `[(nth b (a :: merge <=%R s t0) k), (nth b (a :: merge <=%R s t0) k.+1)])%E).
  rewrite leeD2r//.
  rewrite -merge_ltEle//.
  apply: ih => //.
  move: st.
  by rewrite -cats1 => /cat_sorted2[].
  move=> x xt0.
  apply: tabs.
  by rewrite mem_rcons inE xt0 orbT.
rewrite -addeA.
rewrite leeD2l//.
rewrite cats1 size_rcons.
rewrite -(natr1 (size t0)).
rewrite (EFinD (size t0)%:R) muleDl// mul1e.
have [?|] := boolP (omega_max a b f s \is a fin_num); last first.
  rewrite ge0_fin_numE ?omega_max_ge0//; last first.
    destruct s => //.
    move/itv_partition_nil : abs.
    move: ab => /[swap] ->.
    by rewrite ltxx.
  rewrite -leNgt leye_eq => /eqP abfsy.
  rewrite abfsy.
  rewrite [in leRHS]gt0_muley ?leey//.
  by rewrite lte_paddl//.
rewrite muleDl//.
rewrite leeD2l//.
rewrite lee_pmul//; first exact: oscillation_ge0.
set st0 := merge <=%R s t0.
pose hst0 := fun k => oscillation f `[(nth b (a :: st0) k), (nth b st0 k)].
rewrite (@le_trans _ _ (omega_max a b f (merge <=%R s t0)))//.
  apply: (le_bigmax_seq -oo%E k xpredT hst0) => //.
  rewrite mem_index_iota leq0n/=.
  rewrite /= ltnS in ks.
  by rewrite /st0 -merge_ltEle.
rewrite /omega_max.
rewrite -/st0.
pose hs := fun k => oscillation f `[(nth b (a :: s) k), (nth b s k)].
apply: le_bigmax_seq2 => /= i.
rewrite mem_index_iota leq0n/= => ist0.
move: st; rewrite -cats1 => /cat_sorted2[sorted_t0 _].
have Htmp : forall x, x \in t0 -> (x \in `]a, b[) /\ x \notin s.
  move=> x xt0.
  apply: tabs.
  by rewrite mem_rcons inE xt0 orbT.
rewrite /st0 -merge_ltEle// in ist0.
have [j js H] := itv_partition_mergeS ab abs sorted_t0 Htmp ist0.
exists j => //.
  by rewrite mem_index_iota.
apply: oscillation_sub.
by rewrite /st0 -merge_ltEle.
Qed.

Lemma variation_undup f a b (ab : a < b) s :
  path <=%O a s -> last a s = b ->
  variation a b f s = variation a b f (undup s).
Proof.
elim: s a b ab => // s0 s1 ih a b ab sa asb.
rewrite /=.
destruct s1 as [|s10 s11].
  by simpl.
set s1 := s10 :: s11.
rewrite -/s1 in sa.
rewrite -/s1 in asb.
case: ifPn => s0s1.
  rewrite -/s1 in ih.
  have ? : s10 = s0.
    move: s0s1; rewrite inE => /orP[/eqP //|s0s11].
    apply/eqP; rewrite eq_le; apply/andP; split.
      move: sa => /= /and3P[? ?].
      by move/le_path_min => /allP; apply.
    by move: sa => /= /and3P[? ?].
    subst s10.
  rewrite variation_stutter ih//.
  by move: sa => /= /and3P[->].
rewrite variation_recl.
rewrite [RHS]variation_recl.
congr +%R.
apply: ih => //.
  rewrite /= in asb.
  rewrite -asb.
  rewrite lt_neqAle; apply/andP; split.
    apply/eqP => ?; subst s0.
    by rewrite mem_last in s0s1.
  move: sa.
  rewrite [s1]lock /= -lock => /andP[as0].
  move/order_path_min => /(_ le_trans)/allP; apply.
  by rewrite mem_last.
by move: sa; rewrite /= => /andP[].
Qed.

Lemma merge_filter_undup_alter (s t : seq R) :
  sorted <%R t ->  sorted <%R s ->
  merge <%R s [seq x <- t | [pred x | x \notin s] x] = undup (merge <%R s t).
Proof.
elim: t s => //=.
  move=> s _.
  rewrite merge0r => sorteds.
  rewrite undup_id//.
  apply: sorted_uniq sorteds.
  exact: lt_trans.
  exact: ltxx.
move=> t0 t1 ih s.
elim: s t0 t1 ih => [t0 t1 ih t0t1 /= _|].
  rewrite ifN//; last first.
    move/order_path_min : t0t1 => /(_ lt_trans)/allP t0t1.
    apply/negP => /t0t1.
    by rewrite ltxx.
  rewrite filter_predT undup_id//.
  move/path_sorted : t0t1 => /sorted_uniq; apply.
  exact: lt_trans.
  exact: ltxx.
move=> s0 s1 ih' t0 t1 ih t0t1 sorted_s.
rewrite inE negb_or.
case: ifPn.
  move=> /andP[t0s0 t0s1].
  rewrite /= -!/(merge <%R (s0 :: s1) _).
  have [{}t0s0|] := ltP s0 t0.
    rewrite /=.
    rewrite ifN; last first.
      rewrite mem_merge mem_cat negb_or inE negb_or lt_eqF//=.
      apply/andP; split.
        move: sorted_s => /= => /order_path_min => /(_ lt_trans)/allP H.
        apply/negP => /H.
        by rewrite ltxx.
      move: t0t1 => /= => /order_path_min => /(_ lt_trans)/allP H.
      apply/negP => /H.
      by rewrite ltNge (ltW t0s0).
    congr cons.
    rewrite -ih'//.
    rewrite t0s1//.
    congr merge.
    congr cons.
    apply: eq_in_filter => y yt1.
    rewrite inE negb_or.
    rewrite andb_idl// => ys1.
    move: t0t1 => /= /order_path_min => /(_ lt_trans)/allP => /(_ _ yt1).
    move=> /(lt_trans t0s0) ?.
    by rewrite gt_eqF//.
    move: sorted_s => /=.
    exact: path_sorted.
    rewrite le_eqVlt (negbTE t0s0)/= => {}t0s0.
    rewrite ifN; last first.
      rewrite mem_merge mem_cat !inE !negb_or lt_eqF//=.
    apply/andP; split.
      move: sorted_s => /= => /order_path_min => /(_ lt_trans)/allP H.
      apply/negP => /H.
      by rewrite ltNge (ltW t0s0).
    move: t0t1 => /= => /order_path_min => /(_ lt_trans)/allP H.
    apply/negP => /H.
    by rewrite ltxx.
    congr cons.
    apply: ih => //.
    move: t0t1 => /=.
    by move/path_sorted.
rewrite negb_and !negbK => /predU1P[?|].
  subst t0.
  rewrite /=.
  rewrite /= -!/(merge <%R (s0 :: s1) _).
  rewrite ltxx/= ifT; last first.
    by rewrite mem_merge !inE eqxx.
  rewrite ih//.
  move: t0t1 => /=.
  by apply: path_sorted.
move=> t0s1.
rewrite /= -!/(merge <%R (s0 :: s1) _).
rewrite ifT; last first.
  move: sorted_s => /= => /order_path_min => /(_ lt_trans)/allP.
  by apply.
rewrite /=.
rewrite ifN; last first.
  rewrite mem_merge mem_cat negb_or !inE negb_or.
  apply/and3P; split.
  move: sorted_s => /= => /order_path_min => /(_ lt_trans)/allP H.
  apply/negP => /H.
  by rewrite ltxx.
  rewrite lt_eqF//.
  move: sorted_s => /= => /order_path_min => /(_ lt_trans)/allP.
  exact.
  apply/negP => H.
  move: t0t1 => /order_path_min => /(_ lt_trans)/allP => /(_ _ H) t0s0.
  move: sorted_s => /= => /order_path_min => /(_ lt_trans)/allP => /(_ _ t0s1).
  by rewrite ltNge (ltW t0s0).
rewrite ih//; last first.
  by move: t0t1 => /=; exact: path_sorted.
  transitivity (s0 :: undup (merge <%R s1 t1)).
    rewrite merger_cons//=.
      rewrite mem_merge mem_cat ifN//.
      rewrite negb_or; apply/andP; split.
        move: sorted_s => /= /order_path_min => /(_ lt_trans)/allP H.
        apply/negP => /H.
        by rewrite ltxx.
      move: t0t1 => /= /order_path_min => /(_ lt_trans)/allP H.
      apply/negP => /H => t0s0.
      move: sorted_s => /= /order_path_min => /(_ lt_trans)/allP.
      move/(_ _ t0s1).
      by rewrite ltNge (ltW t0s0).
    apply/allP => x xt1.
    move: sorted_s => /= /order_path_min => /(_ lt_trans)/allP.
    move/(_ _ t0s1) => /lt_le_trans; apply.
    move: t0t1 => /= /order_path_min => /(_ lt_trans)/allP /(_ _ xt1).
    by move/ltW.
congr cons.
rewrite -ih//.
rewrite -ih'//.
rewrite t0s1//=.
by move: sorted_s => /=; apply: path_sorted.
by move: t0t1 => /=; apply: path_sorted.
by move: sorted_s => /=; apply: path_sorted.
Qed.

(* TODO: generalize *)
Lemma lt_merge_lrcons (s t : seq R) (b : R) :
   all (<=%R ^~ b) t -> merge <%R (rcons s b) t = rcons (merge <%R s t) b.
Proof.
elim: t s b; first by move=> ? ?; rewrite 2!merge0r.
move=> + + + s; elim: s => [t0 t1 IH b|s0 s1 IHs t0 t1 IHt b].
  rewrite [all _ _]/= [rcons _ _]/= [merge _ [::] _]/= => /andP[t0b t1b].
  rewrite merge_step ifN; last by rewrite -leNgt.
  have -> : [:: b] = rcons [::] b by []; by rewrite IH.
rewrite [all _ _]/= => /andP[t0b t1b].
rewrite rcons_cons 2!merge_step.
case: ifPn; by [rewrite IHs//= t0b t1b|rewrite -rcons_cons IHt].
Qed.

(* TODO: generalize *)
Lemma le_merge_lrcons (s t : seq R) (b : R) :
  sorted <=%R s -> sorted <=%R t -> (* unnecessary *)
   all (<=%R ^~ b) t -> merge <=%R (rcons s b) t = rcons (merge <=%R s t) b.
Proof.
elim: t s b; first by move=> ? ?; rewrite 2!merge0r.
Abort.
(*
move=> + + + s; elim: s => [t0 t1 IH b _ st |s0 s1 IHs t0 t1 IHt b].
  rewrite [rcons _ _]/= [merge _ [::] _]/= => bt.
  have : t0 <= b. by have/allP := bt; apply; rewrite mem_head.
  rewrite le_eqVlt => /predU1P[t0b|t0b].
    subst b.
    
; rewrite merge_step lexx/=.
  rewrite merge_step ifN; last rewrite -ltNge.
  have -> : [:: b] = rcons [::] b by []; by rewrite IH.
rewrite [all _ _]/= => /andP[t0b t1b].
rewrite rcons_cons 2!merge_step.
case: ifPn; by [rewrite IHs//= t0b t1b|rewrite -rcons_cons IHt].
Qed.
*)

Lemma all_ge_merge1r (t : seq R) (b : R) :
all (<=%R ^~ b) t -> merge <=%R t [:: b] = rcons t b.
Proof.
elim: t => //.
move=> t0 t1 IH /=/andP[t0b t1b]/=.
by rewrite ifT ?IH.
Qed.

Lemma all_gt_merge1r (t : seq R) (b : R) :
all (<%R ^~ b) t -> merge <%R t [:: b] = rcons t b.
Proof.
elim: t => //.
move=> t0 t1 IH /=/andP[t0b t1b]/=.
by rewrite ifT ?IH.
Qed.

(* TODO: generalize? *)
Lemma lt_merge1r_lrcons (s0 : seq R) (s1 : R) (t : R) :
  all (<%R ^~ t) s0 ->
  merge <%R (rcons s0 s1) [:: t] =
    if s1 < t then s0 ++ [:: s1; t] else s0 ++ [:: t; s1].
Proof.
move=> ts0.
case: ifPn => [s1t|].
  rewrite all_gt_merge1r -2?cats1 -?catA ?cat1s//.
  rewrite cats1 all_rcons s1t//.
rewrite -leNgt => ts1.
(*
rewrite merge_lrcons; last by rewrite /= ts1.
by rewrite allrel_merge -?cats1 -?catA ?cat1s ?allrel1r.
Qed.
*)
Abort.

(* TODO: generalize? *)
Lemma le_merge1r_lrcons (s0 : seq R) (s1 : R) (t : R) :
  all (<=%R ^~ t) s0 ->
  merge <=%R (rcons s0 s1) [:: t] =
    if s1 <= t then s0 ++ [:: s1; t] else s0 ++ [:: t; s1].
Proof.
move=> ts0.
case: ifPn => [s1t|].
  rewrite all_ge_merge1r -2?cats1 -?catA ?cat1s//.
  rewrite cats1 all_rcons s1t//.
rewrite -ltNge => ts1.
(*
rewrite merge_lrcons; last by rewrite /= ts1.
by rewrite allrel_merge -?cats1 -?catA ?cat1s ?allrel1r.
Qed.
*)
Abort.

(* TODO: generalize *)
Lemma merge_rcons_step (s0: seq R) (s1 : R) (t0 : seq R) (t1 : R) :
  sorted <=%R (rcons s0 s1) -> sorted <=%R (rcons t0 t1) ->
  merge <%R (rcons s0 s1) (rcons t0 t1) =
  if s1 < t1 then (merge <%R (rcons s0 s1) t0) ++ [:: t1]
             else (merge <%R s0 (rcons t0 t1)) ++ [:: s1].
Proof.
elim/last_ind : t0 s0 => //=.
  move=> s0 // ss0 _.
  case: ifPn => [s1t1|].
  - rewrite merge0r.
    rewrite merge_ltEle//.
    rewrite all_ge_merge1r//; first by rewrite cats1.
    apply/allP => x.
    rewrite mem_rcons in_cons => /predU1P[->|xs0]; first exact: ltW.
    apply/ltW/(le_lt_trans _ s1t1).
    have := ss0.
    rewrite sorted_rconsE/=; last exact: le_trans.
    by move/andP => [_ /allP]; exact.
  - rewrite -leNgt le_eqVlt => /predU1P[t1s1|t1s1].
      subst t1.
      rewrite 2?merge_ltEle//; last first.
        rewrite le_sorted_rconsE in ss0.
        by have/andP[] := ss0.
      rewrite 2?allrel_merge ?cats1//.
        rewrite allrel1r; apply/allP => x xs0.
        by have := ss0; rewrite le_sorted_rconsE => /andP[_ /allP]; exact.
      rewrite allrel1r; apply/allP => x.
      rewrite mem_rcons in_cons => /predU1P[->//|].
      by have := ss0; rewrite le_sorted_rconsE => /andP[_ /allP]; exact.
    rewrite cats1.
    admit.
Abort.

Lemma merge_rrcons (s t : seq R) (b : R) :
   all (<=%R ^~ b) s -> merge <%R s (rcons t b) = rcons (merge <%R s t) b.
Proof.
elim/last_ind : s => //.
Abort.

(*
Lemma merge_rrcons (s t : seq R) (b : R) :
   all (<%R ^~ b) s -> merge <%R s (rcons t b) = rcons (merge <%R s t) b.
Proof.
elim: t s b.
  move=> ? ? ?/=; rewrite merge0r.
  rewrite lt_merge1_max => //.
move=> + + + s; elim: s => [t0 t1 IH b _|s0 s1 IHs t0 t1 IHt b].
  by rewrite [rcons _ _]/= [merge _ [::] _]/=.
rewrite [all _ _]/= => /andP[t0b t1b].
rewrite rcons_cons 2!merge_step.
by case: ifPn; rewrite ?IHs ?IHt//= t0b t1b.
Qed.
*)

Lemma last_undup (s : seq R) (a : R) :
  last a s = last a (undup s).
Proof.
by elim/last_ind : s => // ? ? _; rewrite undup_rcons 2!last_rcons.
Qed.

Lemma last_sorted_merger (s t : seq R) (a : R) :
  all (<=%R ^~ (last a s)) t -> last a (merge <=%R s t) = last a s.
Proof.
(*
elim/last_ind : s abs t'; first by move/(itv_partitionNnil ab).
  move=> s0 s1 IHs + _.
  move=> [pas /eqP]; rewrite last_rcons => ->.
  rewrite merge_lrcons ?last_rcons//.
  by apply/allP => x /tab; rewrite in_itv/= => /andP[_ /ltW].
*)
Abort.

Lemma itv_partition_last_merge a b (ab : a <= b) s t :
  itv_partition a b s ->
  sorted <%R t ->
  (forall x, x \in t -> x \in `]a, b]) ->
  last a (merge <%R s t) = b.
Proof.
elim: t s a b ab => [s a b ab abs _ _|].
  rewrite merge0r.
  by case: abs => _ /eqP.
move=> + + + s.
elim: s => [t0 t1 ih a b ab|].
  move/itv_partition_nil => ba.
  subst b.
  move=> _.
  move/(_ t0).
  rewrite mem_head !in_itv/= => /(_ isT)/andP[at0 t0a].
  have := lt_le_trans at0 t0a.
  by rewrite ltxx.
move=> s0 s1 ih' t0 t1 ih a b ab abs sorted_t tab.
rewrite /=.
have [s0t0|t0s0] := ltP s0 t0.
  rewrite /= (ih' _ _ _ _ b)//.
  rewrite (le_trans (ltW s0t0))//.
  have := tab t0.
  rewrite mem_head => /(_ isT).
  by rewrite in_itv/= => /andP[].
  by apply: itv_partition_cons abs.
  move=> x.
  rewrite inE => /predU1P[->{x}|xt1].
    rewrite in_itv/= s0t0/=.
    have := tab t0.
    rewrite mem_head => /(_ isT).
    by rewrite in_itv/= => /andP[].
  have := tab x.
  rewrite inE xt1 orbT !in_itv/= => /(_ isT)/andP[ax xb].
  rewrite xb andbT.
  rewrite (lt_trans s0t0)//.
  move: sorted_t => /= => /order_path_min => /(_ lt_trans)/allP.
  by apply.
rewrite -/(merge <%R (s0 :: s1) t1).
rewrite /=.
move: t0s0.
rewrite le_eqVlt => /predU1P[?|t0s0].
  subst s0.
  rewrite merger_cons//=; last first.
    move: sorted_t => /= /order_path_min.
    apply.
    exact: lt_trans.
  rewrite (ih _ _ b)//.
  have := tab t0.
  rewrite mem_head => /(_ isT).
  by rewrite in_itv/= => /andP[].
  by apply: itv_partition_cons abs.
  move: sorted_t => /=.
  by apply: path_sorted.
  move=> x xt1.
  have := tab x.
  rewrite inE/= xt1 orbT !in_itv/= => /(_ isT)/andP[ax xb].
  rewrite xb andbT.
  move: sorted_t => /= /order_path_min => /(_ lt_trans)/allP.
  by apply.
rewrite (ih _ _ b)//.
- have := tab t0.
  rewrite mem_head => /(_ isT).
  by rewrite in_itv/= => /andP[].
- split => /=.
    rewrite t0s0/=.
    by case: abs => /= /andP[].
  by case: abs => _ /=.
- by apply: path_sorted sorted_t.
- move=> x xt1.
  rewrite in_itv/=.
  apply/andP; split.
    move: sorted_t => /=.
    by move/order_path_min => /(_ lt_trans)/allP; apply.
  have := tab x.
  by rewrite inE xt1 orbT in_itv/= => /(_ isT)/andP[].
Qed.

Lemma variation_merge f a b (ab : a < b) s t :
  {within `[a, b], continuous f} ->
  itv_partition a b s ->
  sorted <%R t ->
  (forall x, x \in t -> x \in `]a, b[) ->
  ((variation a b f (merge <%R s t))%:E <= (variation a b f s)%:E +
  (size t)%:R%:E * 2 * omega_max a b f s)%E.
Proof.
move=> cf abs sorted_t tab.
pose t' := seq.filter [pred x | x \notin s] t.
have : ((variation a b f (merge <%R s t'))%:E <=
  (variation a b f s)%:E + ((size t')%:R)%:E * 2 * omega_max a b f s)%E.
  apply: variation_merge_notin => //.
  apply: sorted_filter => //.
  exact: lt_trans.
  move=> x.
  rewrite mem_filter => /= /andP[-> xt].
  by rewrite tab.
have -> : variation a b f (merge <%R s t') = (variation a b f (merge <%R s t)).
  rewrite [RHS]variation_undup//.
  - congr variation.
      apply: merge_filter_undup => //.
      by apply: (itv_partition_sorted abs).
    rewrite merge_ltEle; last 2 first.
    + apply: sorted_ltW.
      by have [/path_sorted] := abs.
    + exact: sorted_ltW.
  - apply: merge_path.
      exact: le_total.
    by have [/path_ltW] := abs.
  - rewrite path_min_sorted; first exact: sorted_ltW.
    apply/allP => x /tab.
    by rewrite in_itv/= => /andP[/ltW].
    rewrite (itv_partition_last_merge (ltW ab))// => x .
    move/tab.
    by apply: subset_itv_oo_oc.
move/le_trans; apply.
rewrite leeD2l//.
rewrite lee_pmul//.
  apply: omega_max_ge0.
  apply: itv_partition_neq0 abs.
  by rewrite lt_eqF//.
rewrite lee_pmul// lee_fin ler_nat.
by rewrite size_filter count_size.
Qed.

End variation_merge.

Lemma mem_interval_le (R : realDomainType) (x y a b : R) :
  x \in `[a, b] -> y \in `[a, b] -> `|x - y| <= `|a - b|.
Proof.
rewrite !in_itv/= => /andP[ax xb] /andP[ay yb].
rewrite (@ler0_norm _ (a - b)); last by rewrite subr_le0 (le_trans ax).
rewrite opprB.
have [xy|yx] := leP x y.
  by rewrite ler0_norm ?subr_le0// opprB lerB.
by rewrite gtr0_norm ?subr_gt0// lerB.
Qed.

Lemma bigmaxr_morph {R : realType} n (f : nat -> R) :
  \big[maxr/0]_(0 <= i < n) `|f i| =
  (\big[maxr/0%:nng]_(0 <= i < n)
      `|f i|%:nng)%:num.
Proof.
elim/big_ind2 : _ => //= x1 _ y1 _ -> ->.
rewrite !/maxr.
case: ifPn => x1y1; case: ifPn => // y1x1.
  by apply/eqP; rewrite eq_le (ltW x1y1) andbT leNgt.
by apply/eqP; rewrite eq_le andbC leNgt x1y1/= ltW.
Qed.

Section lemma5.
Context {R : realType}.
Variables (a b : R) (f : R -> R).
Hypothesis (ab : a < b).
Hypothesis cf : {within `[a, b], continuous f}.
Implicit Types (s : seq R) (x : R).

Lemma variation_subseq' s t :
  sorted <=%R s -> sorted <=%R t ->
  subseq s t ->
  variation a b f s <= variation a b f t.
Proof.
elim: s a t.
- move=> ? ? _; by rewrite variation_nil variation_ge0.
move=> + + + + t.
elim: t => //.
move=> t0 t1 IHt s0 s1 IHs a0.
rewrite /= => ps pt.
case: ifPn.
  move/eqP=> s0t0 s1t1.
  subst s0.
  rewrite 2!variation_recl lerD2l.
  apply: IHs => //.
    exact: path_sorted ps.
  exact: path_sorted pt.
move=> s0t0 sst.
apply: (@le_trans _ _ (variation a0 b f t1)).
  apply: IHt => //.
  exact: path_sorted pt.
exact: le_variation.
Qed.

Lemma le_sorted_lt_sorted_undup (s : seq R) :
  sorted <=%R s -> sorted <%R (undup s).
Proof.
move=> ss.
rewrite lt_sorted_uniq_le; apply/andP; split; first exact: undup_uniq.
apply: undup_sorted => //.
exact: le_trans.
Qed.

Lemma lemma5' :
  forall A : R, (0%:E <= A%:E < total_variation a b f)%E ->
    exists2 delta, 0 < delta &
      (forall p, itv_partition a b p ->
       mesh a b p < delta -> (* le? *)
              A < variation a b f p).
Proof.
move=> A /andP[].
rewrite lee_fin => A0.
move/ereal_sup_gt => [_ /=[V' [X' partX' X'V'] <-]].
rewrite lte_fin => AV'.
have : @unif_continuous (subspace `[a, b]) R f.
  exact/compact_unif_continuousP.
move/unif_continuousP => /=.
pose m := size X'.
have mE : m = size X' by [].
pose eps := ((V' - A) / (4 * m)%:R).
have eps0 : 0 < eps.
  rewrite divr_gt0 => //; first by rewrite subr_gt0.
  rewrite -(mulr0n 1) ltr_nat muln_gt0; apply/andP; split => //.
  exact: (itv_partitionNnil ab partX').
move/(_ _ eps0) => [d d0 unifcf].
exists d => // p pabp abpd. (* p is (I) in the paper *)

apply: (@lt_le_trans _ _ ((V' + A) / 2)).
  rewrite ltr_pdivlMr//.
  rewrite -ltrBlDr -{2}(mulr1 A) -mulrBr.
  by rewrite -{2}(mulr1n 1) -natrB// subSnn mulr1.
pose V0 : R := variation a b f (merge <%R p X').
have sleX' : sorted <=%R X' by have [/path_sorted/sorted_ltW] := partX'.
have slep : sorted <=%R p by have [/path_sorted/sorted_ltW] := pabp.
apply: (@le_trans _ _ (V0 - (V' - A) / 2)).
  rewrite [leRHS](_ : _ = V0 - V' + (V' + A) / 2); last first.
    rewrite -[in LHS](@subrK _ V' V0).
    rewrite -(addrA (V0 - V')).
    congr +%R.
    rewrite -mulNr opprD opprK 2!mulrDl addrA.
    congr +%R.
    rewrite -{1}(@mulfK _ 2 _ V')// mulrDr mulr1.
    by rewrite mulrDl mulNr addrK.
  rewrite lerDr subr_ge0.
  rewrite -X'V'.
  apply: variation_subseq' => //.
    rewrite merge_ltEle ?merge_sorted//.
    exact: le_total.
  apply: subseq_merger.
    exact: lt_trans.
  exact: itv_partition_sorted partX'.
rewrite lerBlDr -lee_fin EFinD.
have sorted_X' : (sorted <%R X') by have [/path_sorted] := partX'.
have V0E : V0 = variation a b f (merge <%R p X') by [].
have epsE : eps = (V' - A) / (4 * m)%:R by [].

elim/last_ind : X' partX' X'V' m mE eps epsE eps0 unifcf V0 sleX' V0E sorted_X'.
  by move/(itv_partitionNnil ab).
move=> X'0 X'1 _(* ih *); pose X' := rcons X'0 X'1.
move=> partX' X'V' m mE eps epsE eps0 unifcf V0 sleX' V0E sorted_X'.
have X'E : X' = rcons X'0 X'1 by [].
have X'0ab : (forall x, x \in X'0 -> x \in `]a, b[).
  move=> x xX'0.
  exact: (itv_partition_head_in_itv partX').
have sX'0 : sorted <%R X'0.
  by have[/= + _] := partX'; rewrite rcons_path => /andP[/path_sorted].
have X'1E : X'1 = b.
  have [_] := partX'.
  by rewrite last_rcons => /eqP->.
rewrite V0E.
have[_ /eqP pb] := pabp.
have -> : variation a b f (merge <%R p (rcons X'0 X'1)) =
   variation a b f (merge <%R p X'0).
  rewrite variation_undup//; last 2 first.
  - rewrite merge_ltEle//.
    apply: merge_path => //; last 2 first.
    + by have[/path_ltW] := pabp.
    + by have[/path_ltW] := partX'.
    exact: le_total.
  - rewrite (@itv_partition_last_merge _ _ b)//.
      exact: ltW.
    move=> x; rewrite mem_rcons inE => /predU1P[->|].
      by rewrite X'1E !in_itv/= lexx andbT.
    move/X'0ab.
    exact: subset_itv_oo_oc.
  rewrite [RHS]variation_undup//; last 2 first.
  - rewrite merge_ltEle//; last exact: sorted_ltW.
    apply: merge_path; last 2 first.
    + by have[/path_ltW] := pabp.
    + have[/path_ltW] := partX'.
      by rewrite rcons_path => /andP[].
    exact: le_total.
  - rewrite (@itv_partition_last_merge _ _  _ (ltW ab))//.
    move=> x /X'0ab.
    by apply: subset_itv_oo_oc.
  congr (variation a b f).
  apply: lt_sorted_eq => //.
  - apply: le_sorted_lt_sorted_undup.
    rewrite merge_ltEle//.
    apply: merge_sorted => //.
    exact: le_total.
  - apply: le_sorted_lt_sorted_undup.
    have sorted_X'0 : sorted <=%R X'0.
      by have := sleX'; rewrite le_sorted_rconsE => /andP[].
    rewrite merge_ltEle//.
    apply: merge_sorted => //.
    exact: le_total.
  have sp : sorted <%R p by exact: itv_partition_sorted pabp.
  rewrite -2?merge_filter_undup//.
  rewrite filter_rcons ifN//.
  rewrite negbK.
  have[_ /eqP] := partX'; rewrite last_rcons => ->.
  exact: last_mem_itv_partition pabp ab.
have := @variation_merge _ f a b ab p X'0 cf pabp sX'0 X'0ab.
move/le_trans; apply.
apply: leeD2l.
(* unifcf *)
rewrite -/m.
case: X'0 mE X' X'E partX' X'V' sleX' V0E sorted_X' X'0ab sX'0 => //=.
  by move=> _ _ _ _ _ _ _ _; rewrite 2!mul0e lee_fin divr_ge0// subr_ge0 ltW.
move=> X'00 X'01 mE X' X'E partX' X'V' sleX' V0E sorted_X' X'0ab sX'0.
rewrite -lee_pdivlMl; last first.
  by rewrite mulr_gt0.
rewrite (_ : ((V' - A) / 2) = (m%:R * 2)%R * eps)%R; last first.
  rewrite epsE.
  rewrite (_ : 4 = 2 * 2)%N//.
  rewrite mulnAC 2!natrM.
  rewrite 2!invfM 2!mulrA.
  congr *%R.
  rewrite mulrA.
  rewrite -(mulrA m%:R 2).
  rewrite -(mulrA m%:R (2 * (V' - A))).
  rewrite mulrC.
  rewrite (mulrA m%:R^-1).
  rewrite mulVf ?mul1r; last first.
    apply: lt0r_neq0.
    by rewrite -(mulr0n 1) ltr_nat mE.
  by rewrite mulrAC divff// mul1r.
rewrite /omega_max.
rewrite big_nat_cond.
apply: bigmax_le; first by rewrite leNye.
move=> n.
rewrite leq0n/= andbT => np.
rewrite /oscillation/=.
rewrite -image_comp.
have : compact (f @` `[(nth b (a :: p) n), (nth b p n)]).
  apply: continuous_compact.
    apply: continuous_subspaceW cf.
    apply: subset_itv; rewrite bnd_simp//.
      case: n => //= ? in np *.
      exact/ltW/itv_partition_gt_lb.
    exact: (itv_partition_le_ub pabp).
  exact: segment_compact.
rewrite Rcompact_boundE/= => -[cimg ubimg lbimg].
have nonempty_img : [set f x | x in `[(nth b (a :: p) n), (nth b p n)]] !=set0.
  exists (f (nth b (a :: p) n)) => //.
  exists (nth b (a :: p) n) => //=.
  rewrite boundl_in_itv/= bnd_simp.
  apply/ltW/pathP => //.
  by have [] := pabp.
rewrite ereal_sup_EFin// ereal_inf_EFin//.
rewrite ifN; last first.
  move/set0P : nonempty_img; apply: contra_neq => ->.
  by rewrite image_set0.
rewrite -EFinB lee_fin.

have : forall x y, x \in `[(nth b (a :: p) n), (nth b p n)] ->
 y \in `[(nth b (a :: p) n), (nth b p n)] ->
  `|f x - f y| < eps.
  move=> x y Hx Hy.
  have @x' : subspace `[a, b].
    red.
    exact: x.
  have @y' : subspace `[a, b].
    red.
    exact: y.
  have := unifcf (x', y').
  rewrite /=/ball/=.
  move=> /(_ _).
  apply.
  rewrite /subspace_ball.
  rewrite ifT; last first.
    rewrite inE/=.
    apply: subset_itv Hx; rewrite bnd_simp.
      case: n cimg ubimg lbimg nonempty_img Hy => //=n _ _ _ _ _ in np *.
      exact/ltW/itv_partition_gt_lb.
    exact: (itv_partition_le_ub pabp).
  rewrite /=; split.
    apply: subset_itv Hy; rewrite bnd_simp.
      case: n cimg ubimg lbimg nonempty_img Hx => //=n _ _ _ _ _ in np *.
      exact/ltW/itv_partition_gt_lb.
    exact: (itv_partition_le_ub pabp).
  rewrite /ball/=.
  apply: (@le_lt_trans _ _ `|nth b p n - nth b (a :: p) n|).
    rewrite [in leRHS]distrC.
    exact: mem_interval_le.
  apply: le_lt_trans abpd.
  apply: (@le_trans _ _ (\big[maxr/0]_(0 <= n0 < size p)
      `|nth b p n0 - nth b (a :: p) n0|)); last first.
    by rewrite /mesh/= -bigmaxr_morph.
  apply: (le_bigmax_seq _ _ _ (fun=> _)(*TODO: wtf*)) => //=.
  by rewrite mem_index_iota leq0n.
move=> H.
rewrite lerBlDl; apply: ge_sup => //.
move=> _/= [x px <-].
rewrite -lerBlDr.
apply: lb_le_inf => // _/=[x' px' <-].
rewrite lerBlDr -lerBlDl.
apply: (@le_trans _ _ `|f x - f x'|); first exact: ler_norm.
rewrite 2!mulrA -[leLHS]mul1r.
  apply: ler_pM => //.
  rewrite -mulrA mulrC.
  rewrite -mulf_div divff// mulr1.
  rewrite ler_pdivlMr// mul1r mE.
  by rewrite ler_nat size_rcons.
exact/ltW/H.
Qed.

Definition variations_with_max a b f l : set R :=
   [set r| exists s, [/\ r = variation a b f s,
 itv_partition a b s & (mesh a b s <= l)%R]].

(*lemma5' :
  bounded_variation a b f ->
  forall A : R, (0%:E < A%:E < total_variation a b f)%E ->
    exists l, forall p, itv_partition a b p ->
       itv_partition_max a b p < l -> (* le? *)
              A < variation a b f p. *)

(*
From mathcomp Require Import cardinality.

Definition peaks (g : R -> R) (A : set R) :=
 [set x | x \in A /\
  (\forall y \near x, g y <= g x) \/ (\forall y \near x, g x <= g y)].

Lemma continuous_bounded_variation_countable_peaksP :
  bounded_variation a b f <->
  finite_set (peaks f `[a, b]).
Proof.
split.
- move=> bvf.
  apply/finite_setPn.
  move/pcard_leP/injfunPex => [/= pts sfpts].
  move=> .
  apply: contrapT.
  move/infiniteP.
  move/pcard_injP.
*)

Local Definition lambda_partition (a b : R) (lambda : R) :=
  let n := `|ceil ((b - a) / lambda)|%N in
  [seq (a + (b - a) * i.+1%:R / n%:R) | i <- iota 0 n].

Lemma mesh_lambda x :
  mesh a b (lambda_partition a b x) =
     (b - a) / `|ceil ((b - a) / x)|%N%:R.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite /mesh/=.
  (* apply: bigmax_le. *)
  admit.
Abort.

Lemma itv_partition_lambda x : itv_partition a b (lambda_partition a b x).
Proof.
Abort.

Let divr_ceil_le x : (b - a) / `|ceil ((b - a) / x)|%:R <= x.
Proof.
Abort.

Lemma variations_with_max_lambda x :
   variations_with_max a b f x (variation a b f (lambda_partition a b x)).
Proof.
Abort.
(*
exists (lambda_partition a b x); split => //; first exact: itv_partition_lambda.
rewrite itv_partition_max_lambda.
exact: divr_ceil_le.
Qed.
*)
Lemma total_variation_ex :
  bounded_variation a b f ->
  exists2 p, itv_partition a b p &
       (variation a b f p)%:E = total_variation a b f.
Proof.
Abort.

Lemma variation_with_max0E :
  \forall l \near 0^'+,
  variations_with_max a b f l =
  variations a b f.
Proof.
near=> l.
rewrite eqEsubset; split => A; first by move=> [p [-> pabp _]]; exists p.
move=> [p pabp <-]; exists p; split => //.
apply/eqP; rewrite eq_le; apply/andP; split.
rewrite /total_variation.
Abort.

Definition variations_with_restr a b f l : set R :=
   [set r| exists s, [/\ r = variation a b f s,
 itv_partition a b s & (l <= mesh a b s)%R]].

Lemma variation_with_restr0E l : l <= 0 ->
  variations_with_restr a b f l = variations a b f.
Proof.
move=> l0.
rewrite eqEsubset; split => A; first by move=> [p [? ? _]]; exists p.
move=> [p pabp vA].
exists p; split => //.
apply: (le_trans l0).
exact: mesh_ge0.
Abort.

Lemma lemma5_sup :
  ereal_sup
     [set v%:E | v in variations_with_restr a b f l] @[l --> 0^'+]
     --> total_variation a b f.
Proof.
have -> : total_variation a b f =
   ereal_sup [set v%:E | v in variations_with_restr a b f 0].
  admit.
apply: right_continuousW.
move=> U.
have := (@near_cst_continuous _ _ (total_variation a b f)
  (fun l : R => ereal_sup [set v%:E | v in variations_with_restr a b f l]) 0).
Abort.

Lemma variations_with_max_restr :
\forall l \near 0^'+,
  (ereal_inf
     [set v%:E | v in variations_with_max a b f l]
  <= ereal_sup
     [set v%:E | v in variations_with_restr a b f l])%E.
Proof.
near=> l.
apply: le_ereal_sup_tmp.
exists (total_variation a b f).
Abort.

Lemma lemma5 (l : nat -> R) (x_ : nat -> seq R) :
  (forall n, itv_partition a b (x_ n)) ->
  (forall n, mesh a b (x_ n) <= l n) ->
  l i @[i --> \oo] --> 0 ->
  (variation a b f (x_ n))%:E @[n --> \oo] --> total_variation a b f.
Proof.
move=> pabx xl lcvg0.
have vletv n : ((variation a b f (x_ n))%:E <= total_variation a b f)%E.
  apply: le_ereal_sup_tmp.
  exists (variation a b f (x_ n))%:E => //=.
  exists (variation a b f (x_ n))=> //.
  by exists (x_ n).
have := total_variation_ge0 f (ltW ab).
rewrite le_eqVlt => /predU1P[tvf0|tvfgt0].
  apply: cvg_near_cst; apply: nearW => n.
  apply/eqP; rewrite eq_le; apply/andP; split => //.
  by rewrite -tvf0; exact: variation_ge0.
have [tvfoo|] := eqVneq (total_variation a b f) +oo%E.
  rewrite tvfoo.
  move=> /= U.
  rewrite /nbhs/= => -[A [_ HA]].
  have [A0|A0] := ltP A 0.
    exists 0%N => // k/= => _; apply: HA.
    by rewrite (@lt_le_trans _ _ 0%E)// lee_fin variation_ge0.
  have : (0%:E <= A%:E < total_variation a b f)%E.
    by rewrite lee_fin A0 tvfoo ltry.
  move/lemma5' => /=[e e0].
  have lne : \forall n \near \oo, l n < e.
    move: lcvg0.
    move/(cvgr_dist_lt _ 0) /(_ e e0).
    under eq_near => n.
      rewrite sub0r normrN ger0_norm; last first.
        by rewrite (le_trans _ (xl _))// mesh_ge0.
      over.
    by [].
  have mxe : \forall n \near \oo, mesh a b (x_ n) < e.
    apply: filterS lne => n.
    exact: le_lt_trans.
  move=> abA.
  apply: filterS mxe.
  move=> n /abA => /(_ (pabx n)).
  by rewrite -lte_fin => /HA.
rewrite -ltey.
move=> tvfltey.
have tvf_fin : total_variation a b f \is a fin_num.
  rewrite ge0_fin_numE => //.
  exact: (total_variation_ge0 _ (ltW ab)).
rewrite -(@fineK _ (total_variation a b f)) => //.
apply/fine_cvgP.
split => //.
  exact: nearW.
apply/cvgrPdist_ltp.
near=> e.
have : (0%:E <= (fine (total_variation a b f) - e)%:E < total_variation a b f)%E.
  apply/andP; split; rewrite ?lee_fin.
    rewrite subr_ge0; near: e.
    apply: nbhs_right_le.
    by rewrite fine_gt0// tvfgt0.
  rewrite EFinB fineK//.
  by rewrite gte_subl// lte_fin.
move/lemma5' => [d d0 H].
near=> n.
rewrite ger0_norm; last by rewrite subr_ge0 -lee_fin !fineK.
rewrite ltrBlDl -ltrBlDr/=.
apply: (H) => //.
apply: (le_lt_trans (xl n)).
near: n.
exact: (cvgr_lt _ lcvg0 _ d0).
Unshelve. all: end_near. Qed.

(*
Lemma lemma5_cvg_style :
(*  {within `[a, b], continuous f} ->*)
  ereal_inf
     [set v%:E | v in variations_with_max a b f l] @[l --> 0^'+]
       --> total_variation a b f.
Proof.
have [|] := eqVneq (total_variation a b f) +oo%E.
  move=> tvfoo; rewrite tvfoo.
  apply/cvgeyPgey.
  near=> A.
  have : (0%:E <= A%:E < total_variation a b f)%E.
    by rewrite lee_fin tvfoo ltry andbT.
  move/lemma5' => /=[l l0 Hl].
  exists l => // x/=.
  rewrite sub0r normrN.
  move/ltr_normlW => xl x0.
  apply/ereal_infP => _ [_ [s [-> pabs sx]] <-].
  rewrite lee_fin; apply: ltW.
  apply: Hl => //.
  exact: le_lt_trans xl.
rewrite -ltey => bvf.
suff H : inf (variations_with_max a b f l) @[l --> 0^'+] -->
    sup (variations a b f).
  rewrite /total_variation ereal_sup_EFin; last 2 first.
  - exists (fine (total_variation a b f)) => _ [s ps <-].
    rewrite -lee_fin fineK; last first.
      rewrite ge0_fin_numE//.
      apply: total_variation_ge0.
      exact: ltW.
    exact: variation_le_total_variation.
  - exists `|f b - f a|.
    exists [:: b].
      exact: itv_partition1.
    by rewrite /variation/= big_seq1.
  apply: cvg_EFin.
    apply: nearW => l.
    rewrite ge0_fin_numE => //; last first.
      apply: le_ereal_inf.
    admit.
  under eq_cvg => l/=.
    rewrite ereal_inf_EFin/=; last 2 first.
    - admit.
    - admit.
    over.
  done.
  apply/cvg_at_rightP => l [l0 cvgl].
apply/cvgrPdist_le => /= e e0.
have : (0%:E <= (fine (total_variation a b f) - e)%:E < total_variation a b f)%E.
  admit.
move/lemma5' => /= [L L0 HL].
have := cvgl (ball 0 L) (nbhsx_ballx _ _ L0).
  move=> [m _ mL].
near=> n.
rewrite gtr0_norm; last first.
  rewrite subr_gt0.
  apply: (@lt_le_trans _ _ (sup (variations_with_max a b f (l n)))).
    apply: has_bound_not_subset1_inf_sup.
        exists 0 => /= _ [? [-> _ _]].
        exact: variation_ge0.
      exists (fine (total_variation a b f)).
      move=> v [s [-> pabs _]].
      rewrite -lee_fin fineK; last first.
        rewrite ge0_fin_numE//.
        exact/total_variation_ge0/ltW.
      apply: le_ereal_sup_tmp.
      exists (variation a b f s)%:E => //.
      exists (variation a b f s) => //.
      by exists s.
    rewrite -existsNE.
    have : exists k, l k < l n.
      move: cvgl.
      move/(_ (ball 0 (l n))).
      move/(_ (nbhsx_ballx _ _ (l0 n))).
      move=> [k _].
      move/(_ k (leqnn k)).
      rewrite /ball/= sub0r normrN gtr0_norm// => lkn.
      by exists k.
    move=> [k lkn].
    exists (variation a b f (lambda_partition a b (l n))).
    rewrite -existsNE.
    exists (variation a b f (lambda_partition a b (l k))).
    apply/not_implyP; split; last (apply/not_implyP; split).
    - exact: variations_with_max_lambda.
    - exists (lambda_partition a b (l k)); split => //.
        exact: itv_partition_lambda.
      rewrite itv_partition_max_lambda.
        apply: ltW.
        apply: le_lt_trans lkn.
        exact: divr_ceil_le.
    admit.
  apply: sup_le; last 2 first.
  - exists (variation a b f (lambda_partition a b (l n))).
    exact: variations_with_max_lambda.
  - split.
      exists (variation a b f [:: b]).
      exists [:: b] => //.
      exact: itv_partition1.
    exists (fine (total_variation a b f)) => _ [s ps <-].
    rewrite -lee_fin fineK; last first.
      by rewrite ge0_fin_numE ?total_variation_ge0 ?ltW.
    exact: variation_le_total_variation.
  move=> _ [s [-> ps _]].
  exists (variation a b f s); split => //.
  exact: variations_variation.
rewrite lerBlDr -lerBlDl.
rewrite -lee_fin.
rewrite -ereal_inf_EFin; last 2 first.
- admit.
- admit.
apply: le_ereal_inf_tmp.
move=> _ [_ [s [-> ps sl] <-]].
rewrite EFinB -ereal_sup_EFin; last 2 first.
- admit.
- admit.
rewrite -[X in (X - _ <= _)%E]fineK; last first.
  admit.
rewrite lee_fin.
apply: ltW.
apply: HL => //.
apply: (le_lt_trans sl).
have : (m <= n)%N.
  near: n.
  exact: nbhs_infty_ge.
move/(mL n) => /=.
by rewrite/ball/= sub0r normrN gtr0_norm.
Unshelve. all: end_near. Admitted.

(* from old lemma6 proof *)
(*
rewrite -{1}(@fineK _ (total_variation a b f)); last first.
  by apply/bounded_variationP => //; exact: ltW.
move/fine_cvgP => [fin_inf].
move/cvg_at_rightP.
move/(_ lambda).
have Hlambda : (forall n : nat, 0 < lambda n) /\ lambda n @[n --> \oo] --> 0.
  split; last exact: cvg_lambda0.
  move=> k.
  exact: lambda_gt0.
move/(_ Hlambda); move{Hlambda} => Hl.
apply: squeeze_cvgr _ Hl (cvg_cst Vcd).
near=> n.
apply/andP; split; last first.
  rewrite /Vcd/total_variation.
  rewrite -lee_fin fineK; last by apply/bounded_variationP => //; exact: ltW.
  apply: le_ereal_sup_tmp.
  exists (S_ n)%:E => //.
  exists (S_ n) => //.
  by exists (x n).
rewrite -lee_fin fineK; last first.
  have := fin_inf.
  move=> [l /= l0].
  apply => //=.
  rewrite sub0r normrN ger0_norm; last first.
    exact/ltW/lambda_gt0.
  move: l l0; near: n.
  admit.
  exact: lambda_gt0.
apply: ge_ereal_inf.
exists (S_ n)%:E => //.
exists (S_ n) => //.
by exists (x n); split.
Unshelve. end_near. Admitted.
*)

have [tvfoo|] := eqVneq (total_variation a b f) +oo%E.
  rewrite tvfoo.
  admit.
have -> : total_variation a b f
    = ereal_inf [set v%:E | v in variations_with_max a b f 0].
  rewrite /total_variation.
  admit.
*)

End lemma5.
