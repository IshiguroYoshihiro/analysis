From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean perm finmap.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions contra cardinality.
From mathcomp Require Import reals topology normedtype ereal sequences derive.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import absolute_continuity.

(**md**************************************************************************)
(* # interleave                                                               *)
(*                                                                            *)
(* seq_of_pair  := reshape sequences of a pair into sequences of sequences    *)
(*                 which contains two elements.                               *)
(* interleave s t := A sequence formed by alternating the first (min s t)     *)
(*                   elements from columns s and t.                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section seq_of_pair.

Definition seq_of_pair {T} (s : seq (T * T)) : seq (seq T) :=
  [seq [:: ab.1; ab.2] | ab <- s].

Lemma shape_seq_of_pairs {T} (s : seq (T * T)) :
  shape (seq_of_pair s) = nseq (size s) 2.
Proof. by elim: s => [|[x y] s IH] //=; rewrite IH. Qed.

Lemma sorted_seq_of_pairP {T : eqType} (e : rel T) (st : seq (T * T)) :
  transitive e ->
  (sorted e (flatten (seq_of_pair st))) <->
    [/\ (forall i d, (i < (size st))%N ->
                 e (nth d (unzip1 st) i) (nth d (unzip2 st) i)) &
     (forall i d, (i.+1 < (size st))%N ->
              e (nth d (unzip2 st) i) (nth d (unzip1 st) i.+1))].
Proof.
move=> te.
elim: st => // st0 st [IH1 IH2]; split.
  move=> /=/andP[st0le]; rewrite path_sortedE => // /andP[st02st].
  move/IH1 => [st12 st21]; split => i d.
    by case: i => //= n; rewrite ltnS; move/st12; apply.
  rewrite ltnS; case: i => /= [sizest0|n sizest_n1].
    move: st02st => /allP; apply.
    move: sizest0; clear; case: st => //; move=> st0 st /= _.
    by rewrite in_cons eqxx.
  exact: st21.
move=> /= [st12 st21]; apply/andP; split.
  by move: (st12 0 st0.1 isT).
apply/(pathP st0.1) => -[|].
  by move: st21; clear; case: st => // st1 st /(_ 0 st0.1).
apply/sortedP/IH2; split => i d.
  exact: (st12 i.+1 d).
exact: (st21 i.+1 d).
Qed.

(* for le_sorted_interleave. unnecessary? *)
Lemma sorted_seq_of_pairP' {T : eqType} (e : rel T) (st : seq (T * T)) :
  reflexive e ->
  transitive e ->
  (sorted e (flatten (seq_of_pair st))) <->
    [/\ (forall i d, e (nth d (unzip1 st) i) (nth d (unzip2 st) i)) &
     (forall i d, (i.+1 < (size st))%N ->
              e (nth d (unzip2 st) i) (nth d (unzip1 st) i.+1))].
Proof.
move=> re te.
split.
  move/(sorted_seq_of_pairP _ te) => [H1 H2]; split => // i d.
  have [|] := ltnP i (size st).
    by move/H1.
  by move=> sti; rewrite !nth_default// size_map.
move=> [H1 H2]; exact: (sorted_seq_of_pairP _ te).2.
Qed.

End seq_of_pair.

Section interleave_def.

Fixpoint interleave {T} (s t : seq T) :=
  match s, t with
  | x :: s', y :: t' => x :: y :: interleave s' t'
  | _, _ => [::]
  end.

Lemma interleaveE {T} (s t : seq T) :
  interleave s t = flatten (seq_of_pair (zip s t)).
Proof. by elim: s t => [|x s' IH] [|]// y t'//=; rewrite IH. Qed.

End interleave_def.

Section interleave_lemmas.

Lemma size_interleave {T} (s t : seq T) :
   (size (interleave s t) = (minn (size s) (size t)).*2)%N.
Proof.
by rewrite interleaveE size_flatten shape_seq_of_pairs sumn_nseq size_zip mul2n.
Qed.

Lemma interleave0s {T} (t : seq T) :
  interleave [::] t = [::].
Proof. by []. Qed.

Lemma interleaves0 {T} (s : seq T) :
  interleave s [::] = [::].
Proof. by elim: s. Qed.

Lemma interleave_cons {T} (x y : T) (s t : seq T) :
  interleave (x :: s) (y :: t) = x :: y :: interleave s t.
Proof. by []. Qed.

Lemma subseq_interleaver {T : eqType} (s t : seq T) :
  (size s <= size t)%N ->
   subseq s (interleave s t).
Proof.
elim: s t.
  by move=> ? _; apply: sub0seq.
move=> s0 s1 IHs.
case => // t0 t1; rewrite [X in X -> _]/= ltnS => st.
rewrite interleave_cons -(cat1s s0) -(cat1s s0 (t0 :: _)) subseq_cat2l.
apply: (@subseq_trans _ (interleave s1 t1)).
  exact: IHs.
exact: cons_subseq.
Qed.

Lemma subseq_interleavel {T : eqType} (s t : seq T) :
  (size t <= size s)%N ->
   subseq t (interleave s t).
Proof.
elim: s t; first by case.
move=> s0 s1 IHs.
case => // t0 t1; rewrite [X in X -> _]/= ltnS => ts.
rewrite interleave_cons.
apply: (@subseq_trans _ (t0 :: (interleave s1 t1))).
  by rewrite /= ifT//; apply: IHs.
exact: cons_subseq.
Qed.

Lemma mem_interleaver {T : eqType} (s t : seq T) :
  (size s <= size t)%N ->
  forall x, x \in s -> x \in interleave s t.
Proof.
elim: s t => //=.
move=> s0 s1 IHs.
case => // t0 t1; rewrite [X in X -> _]/= ltnS => s1t1 x.
rewrite !in_cons => /predU1P[->|xs1].
  by apply/orP; left.
by apply/orP; right; apply/orP; right; apply: IHs.
Qed.

Lemma mem_interleavel {T : eqType} (s t : seq T) :
  (size t <= size s)%N ->
  forall x, x \in t -> x \in interleave s t.
Proof.
elim: t s => //=.
move=> t0 t1 IHt.
case => // s0 s1; rewrite [X in X -> _]/= ltnS => t1s1 x.
rewrite interleave_cons !in_cons => /predU1P[->|xs1].
  by apply/orP; right; apply/orP; left.
by apply/orP; right; apply/orP; right; apply: IHt.
Qed.

Lemma perm_interleave {T : eqType} (s t : seq T) :
  size s = size t ->
  perm_eq (interleave s t) (s ++ t).
Proof.
elim: s t.
  by move=> t /=/esym/size0nil ->.
move=> s0 s1 IHs.
case => // t0 t1.
rewrite [X in X -> _]/= => /eq_add_S s1t1.
rewrite interleave_cons /= perm_cons.
rewrite -[X in _ _ (_ ++ X)]cat1s perm_sym perm_catCA cat1s perm_cons perm_sym.
exact: IHs.
Qed.

Lemma mem_interleave {T : eqType} (s t : seq T) :
  size s = size t ->
  interleave s t =i s ++ t.
Proof.
move=> st; apply: perm_mem.
exact: perm_interleave.
Qed.

Lemma le_sorted_interleavel d {T : porderType d} (s t : seq T) :
  (size s <= size t)%N ->
   sorted <=%O (interleave s t) -> sorted <=%O s.
Proof.
elim: s t => // s0 s1 IH; case => // t0 t1.
rewrite [X in X -> _]/= ltnS => s1t1; rewrite interleave_cons/= => /andP[s0t0].
rewrite !le_path_sortedE => /andP[/allP t0st sst]; apply/andP; split.
  by apply/allP => ? ?; apply: (le_trans s0t0); apply: t0st; apply: mem_interleaver.
exact: (IH _ s1t1).
Qed.

Lemma le_sorted_interleaver d {T : porderType d} (s t : seq T) :
  (size t <= size s)%N ->
   sorted <=%O (interleave s t) -> sorted <=%O t.
Proof.
elim: t s => // t0 t1 IH; case => // s0 s1.
rewrite [X in X -> _]/= ltnS => t1s1; rewrite interleave_cons/= => /andP[s0t0].
rewrite !le_path_sortedE => /andP[/allP t0st sst]; apply/andP; split.
  by apply/allP => ? ?; apply: t0st; apply: mem_interleavel.
exact: (IH _ t1s1).
Qed.

Lemma le_sorted_interleaveP d {T : porderType d} (s t : seq T) :
  size s = size t ->
  (sorted <=%O (interleave s t)) <->
   ((forall i d, nth d s i <= nth d t i)%O /\
     (forall i d, (i.+1 < (size s))%N -> nth d t i <= nth d s i.+1)%O).
Proof.
move=> st; rewrite interleaveE.
rewrite -{-1}(unzip1_zip (eq_leq st)) size_map -{3 5}(@unzip2_zip _ _ s t)?st//.
exact/sorted_seq_of_pairP'/le_trans/le_refl.
Qed.

Lemma lt_sorted_interleaveP d {T : porderType d} (s t : seq T) :
  size s = size t ->
  (sorted <%O (interleave s t)) <->
   (forall (i : nat) d, (i < (size s))%N -> nth d s i < nth d t i)%O /\
     (forall i d, (i.+1 < (size s))%N -> nth d t i < nth d s i.+1)%O.
Proof.
move=> st; rewrite interleaveE.
rewrite -{-1}(unzip1_zip (eq_leq st)) size_map -{4 6}(@unzip2_zip _ _ s t)?st//.
apply/sorted_seq_of_pairP/lt_trans.
Qed.

Lemma interleave_merge d {T : orderType d} (s t : seq T) :
  size s = size t ->
  sorted <=%O (interleave s t) ->
  interleave s t = merge <=%O s t.
Proof.
move=> st /[dup]sorted_st.
have srts : sorted <=%O s by exact: (le_sorted_interleavel (eq_leq st)).
have srtt : sorted <=%O t by exact: (le_sorted_interleaver (eq_leq (esym st))).
move/le_sorted_interleaveP => []// slet tles1.
apply: le_sorted_eq => //.
  apply: merge_sorted => //.
  exact: le_total.
rewrite perm_sym perm_merge perm_sym.
exact: perm_interleave.
Qed.

Lemma nth_interleaveE {T} (d : T) (s t : seq T) n :
  nth d (interleave s t) n =
    if (n < size (interleave s t))%N then
      if odd n then nth d t n./2 else nth d s n./2
    else d.
Proof.
elim: s t n => [|x s IH] [|y t] [|[|n]] //=.
by rewrite negbK; exact: IH _ n.
Qed.

Lemma last_interleave {T} (d : T) (s t : seq T) :
  (size t <= size s)%N ->
  last d (interleave s t) = last d t.
Proof.
move=> ts.
have size_st : size (interleave s t) = (size t).*2.
  rewrite size_interleave /minn ifF//.
  by apply/negP/negP; rewrite -leqNgt.
rewrite -!nth_last nth_interleaveE.
case: ifP; rewrite ltn_predL; last first.
  move/negP/negP; rewrite -eqn0Ngt size_st double_eq0.
  by move/eqP => t0; rewrite nth_default ?t0.
rewrite size_st/=.
set n := size t; have : n = size t by [].
case: n => //n nt _/=.
by rewrite odd_double/= uphalf_double.
Qed.

End interleave_lemmas.

Section flatten_lemmas.
Context d {T : porderType d}.

Lemma nth0_flatten_interleave def (ss tt : (seq (seq T))) :
  head [::] ss != [::] ->
  (size ss <= size tt)%N ->
  nth def (flatten (interleave ss tt)) 0 = nth def (nth [::] ss 0) 0.
Proof.
elim: ss tt => //=.
move=> s ss IH.
case => // t tt s0 sstt.
rewrite nth_cat ifT//.
apply/not_notP => /negP; rewrite -leqNgt leqn0 => /eqP/size0nil/eqP.
by apply/negP.
Qed.

Lemma last_flatten_interleave def (ss tt : (seq (seq T))) :
  all (fun s => s != [::]) ss ->
  all (fun s => s != [::]) tt -> (* generalize? *)
  (size tt <= size ss)%N ->
  last def (flatten (interleave ss tt)) = last def (last [::] tt).
Proof.
elim: tt ss def.
  move=> ss def _ _ _.
  by rewrite interleaves0.
move=> t tt IH.
case => // s ss def ss0 tt0 ttss.
rewrite interleave_cons/=.
rewrite !last_cat.
rewrite IH//.
- by move/andP: ss0; case.
- by move/andP: tt0; case.
have [->/=|] := eqVneq tt [::].
  apply: set_last_default.
  rewrite ltnNge leqn0.
  apply/negP; move/eqP/size0nil/eqP; apply/negP.
  by move/andP: tt0; case.
move=> tt_neq_nil.
rewrite (@set_last_default _ tt [::]).
  rewrite ltnNge leqn0.
  by apply/negP; move/eqP/size0nil/eqP; apply/negP.
apply: set_last_default.
rewrite ltnNge leqn0.
apply/negP; move/eqP/size0nil/eqP; apply/negP.
move/andP: tt0 => [_ /allP]; apply.
rewrite -nth_last mem_nth// ltn_predL.
rewrite ltnNge leqn0.
by apply/negP; move/eqP/size0nil/eqP; apply/negP.
Qed.

End flatten_lemmas.

Section flatten_bigop.

(*
Lemma variation_cat_last {R : realDomainType} a b f (s t : seq R) :
  variation a b f (s ++ t) =
  variation a b f s + variation (last a s) b f t.
Proof.
elim: s a.
  by move=> ?; rewrite variation_nil add0r.
by move=> ? ? IH ?; rewrite !variation_recl IH addrA.
Qed.
*)

Print GRing.monoid_morphism.
Lemma bigop_flatten_interleave_split
  {T0 : eqType} {T1 : Type} (idx : T1) (op : Monoid.com_law idx) (def : T0)
    (F : seq T0 -> T1) (x : T0) (s t : seq (seq T0)) :
   F [::] = idx -> {morph F : x y / x ++ y >-> op x y} ->
    all (fun u => u != [::]) (s ++ t) ->
  \big[op/idx]_(i < size (s ++ t)) F (flatten (interleave s t)) =
    op
      (\big[op/idx]_(i < minn (size s) (size t))
        F ((nth def [seq last def u | u <- [:: x] :: t] i) :: (nth [::] s i)))
      (\big[op/idx]_(i < minn (size s) (size t))
        F ((nth def [seq last def u | u <- s] i) :: (nth [::] t i))).
Proof.
move=> F0 mF.
rewrite all_cat.
elim: s t x.
  case.
    move=> t x/=.
    by rewrite F0 !big_ord0 Monoid.mul1m.
  move=> t0 t1 x/=.
  rewrite F0 !big_ord0 Monoid.mul1m big_const_idem//.
  by have := (@Monoid.mul1m T1 idx op idx).
move=> s0 s1 IH.
case => /=.
  move=> x.
  rewrite F0 !big_ord0 Monoid.mul1m big_const_idem//.
  by have := (@Monoid.mul1m T1 idx op idx).
move=> t0 t1 x.
move=> /andP[/andP[s00 s10] /andP[t00 t10]].

(*
rewrite /= !variation_cat_last.
have -> : last a x = last def x by case: x x0.
have -> : last (last def x) y = last def y by case: y y0.
rewrite (IH B (last def y) _) ?minnSS ?A0 ?B0// !big_ord_recl /= addrA addrACA.
by congr (_ + _ + (_ + _)); apply: variation_any_ub.
*)
Abort.

End flatten_bigop.
