From HB Require Import structures.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import interval archimedean.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets contra.
From mathcomp Require Import reals topology ereal normedtype.
From mathcomp Require Import numfun realfun.
From mathcomp Require Import bz_mathcomp_extra interleave merge_extra.
From mathcomp Require Import absolute_continuity. (*NB: to get has_bound_inf_sup*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

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
  rewrite nth_index.
    by rewrite in_cons; apply/orP; right.
    move/[swap] => _.
    rewrite -last_nth last_rcons => xb.
  rewrite ifN.
    by rewrite lt_eqF// asb.
  rewrite (_ : index x (rcons s b) = index x s).
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
  rewrite ifF.
    rewrite lt_eqF => //.
    have [/lt_path_min/allP + _] := pst.
    by apply; rewrite mem_rcons in_cons xs orbT.
  by rewrite size_rcons -cats1 index_cat xs ltnS index_mem.
rewrite inE index_mem.
rewrite in_cons; apply/orP; right.
by rewrite mem_rcons in_cons xs orbT.
Qed.

Lemma itv_partition_gt_lb def a b s : (a < def)%O ->
  itv_partition a b s -> forall n, (a < nth def s n)%O.
Proof.
move=> ab ps n.
have [ns|ns] := ltnP n (size s).
  suff : nth def s n \in `]a, b].
    by rewrite in_itv/= => /andP[].
  apply: (itv_partition_in_itv ps).
  exact: mem_nth.
by rewrite nth_default.
Qed.

Lemma itv_partition_le_ub def a b s :
  itv_partition a b s -> forall n, (n < size s)%N -> (nth def s n <= b)%O.
Proof.
move=> ps n ns.
suff : nth def s n \in `]a, b].
  by rewrite in_itv/= => /andP[].
apply: (itv_partition_in_itv ps).
by apply/mem_nth.
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

Section itv_partition_order.
Context {d} {T : orderType d}.
Implicit Types (a b x : T) (s : seq T).

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

End itv_partition_order.

Section variation_merge.
Context {R : realType}.
Implicit Type (f : R -> R).
Implicit Types (s : seq R) (x : R).

Lemma merge1E s h : h \notin s -> sorted <%O s ->
  merge <%O s [:: h] = itv_partitionL s h ++ itv_partitionR s h.
Proof.
move=> hs ss; apply: (@irr_sorted_eq _ <%O) => //.
- exact: lt_trans.
- exact: sorted_merge1.
- have sE := notin_itv_partition ss hs.
  rewrite /itv_partitionL -cats1 -catA/= sorted_cat_cons.
  rewrite notin_sorted_rcons//= path_min_sorted//.
    by apply/allP => x; rewrite mem_filter => /andP[].
  by apply: sorted_filter => //; exact: lt_trans.
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
- exact: itv_partition_sorted abs.
- apply: itv_partition_cat.
    exact: itv_partitionLP abs.
  exact: itv_partitionRP abs.
Qed.

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
rewrite merge_ltEle.
- apply: sorted_ltW.
  by have[/path_sorted] := abs.
- by rewrite cats1 sorted_ltW.
rewrite (@merge_cats1 _ _ s t0 t1).
- by apply: sorted_ltW; exact: (itv_partition_sorted abs).
- by rewrite cats1 sorted_ltW.
rewrite -merge_ltEle//.
- apply: merge_sorted; rewrite ?sorted_ltW//.
      exact: le_total.
    by have [/path_sorted] := abs.
  rewrite sorted_rconsE in sorted_t; first exact: lt_trans.
  by have/andP[] := sorted_t.
apply: itv_partition_merge1 => //.
  apply ts.
  by rewrite mem_rcons mem_head.
rewrite mem_merge mem_cat negb_or; apply/andP; split.
  apply ts.
  by rewrite mem_rcons mem_head.
  by apply: lt_sorted_rcons_notin sorted_t.
rewrite -merge_ltEle.
    by have [/path_ltW/path_sorted] := abs.
  rewrite sorted_rconsE in sorted_t; first exact: lt_trans.
  by have/andP[/sorted_ltW] := sorted_t.
apply: ih => //.
move: sorted_t.
rewrite -cats1.
by move/cat_sorted2 => -[].
move=> x xt0.
apply: ts.
by rewrite mem_rcons inE xt0 orbT.
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
have [k K1 K2] := @itv_partition_notin_inbetween a b (merge <%R s t0) t H0 H1 H2.
by exists k.
Qed.

End variation_merge.

Lemma itv_partition_mergeS {R : realType} def a b (s t : seq R) : (a < b)%R ->
  itv_partition a b s ->
  sorted <%R t ->
  (forall x, x \in t -> (x \in `]a, b[) /\ x \notin s) ->
  forall i, (i < size (merge <%R s t))%N ->
  exists2 j, (j < size s)%N &
  `[(nth def (a :: merge <%R s t) i), (nth def (merge <%R s t) i)]
  `<=`
  `[(nth def (a :: s) j), (nth def s j)].
Proof.
elim : t def s a b => [def s a b ab abs _ abt i|t0 t1 ih def].
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
    have : nth def (t0 :: t1) i \in t0 :: t1 by apply/(nthP def); exists i.
    move/abt => [+ _].
    by rewrite in_itv/= => /andP[_ /ltW].
  rewrite /= ltnS => ist.
  have s0bs1 := itv_partition_cons abs.
  have : exists2 j : nat,
     (j < size s1)%N &
     `[(nth def (s0 :: merge <%R s1 (t0 :: t1)) i),
     (nth def (merge <%R s1 (t0 :: t1)) i)]
     `<=` `[(nth def (s0 :: s1) j), (nth def s1 j)].
    apply: ih' => //.
      exact: s0b.
      by [].
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
    have : nth def (merge <%R [:: b] t1) i \in b :: t1.
      rewrite -[X in _ \in X]cat1s.
      rewrite -(mem_merge <%R).
      apply/(nthP def); exists i => //.
      by rewrite (leq_trans _ ist)//.
    rewrite inE => /predU1P[->|h].
      exact/ltW.
    have := abt (nth def (merge <%R [:: b] t1) i).
    rewrite inE h orbT => /(_ isT)[].
    by rewrite in_itv/= => /andP[/ltW].
  rewrite (le_trans xi)//.
  have : nth def (merge <%R [:: b] t1) i \in b :: t1.
    rewrite -[X in _ \in X]cat1s.
    rewrite -(mem_merge <%R).
    by apply/(nthP def); exists i.
  rewrite inE => /predU1P[->//|h].
  have := abt (nth def (merge <%R [:: b] t1) i).
  rewrite inE h orbT => /(_ isT)[].
  by rewrite in_itv/= => /andP[_ /ltW].
have sorted_t1 : sorted <%R t1.
  by apply: path_sorted t0t1.
have Htmp : (forall x, x \in t1 -> (x \in `]a, b[) /\ x \notin (s0 :: s1)).
  move=> x xt2.
  apply: abt.
  by rewrite inE xt2 orbC.
have [j Hj Hj']:= ih def _ _ _ ab abs sorted_t1 Htmp _ ist.
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

Lemma itv_partition_last_merge {R : realType} (a b : R) (ab : a <= b) s t :
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
  rewrite merger_cons//=.
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

Section variation_lemmas.

Lemma variationxx {R : numDomainType} a b (f : R -> R) s :
  variation a b f (a :: s) = variation a b f s.
Proof. by rewrite /variation/= big_nat_recl//= subrr normr0 add0r. Qed.

Lemma variation_stutter {R : numDomainType} a b (f : R -> R) x s :
  variation a b f [:: x, x & s] = variation a b f (x :: s).
Proof.
rewrite /variation.
rewrite [x :: s]lock /= big_nat_recl// -lock.
by rewrite /= !big_nat_recl//= subrr normr0 add0r.
Qed.

Lemma variation_recr {R : numDomainType} a b (f : R -> R) s :
  variation a b f (rcons s (last a s)) = variation a b f s.
Proof.
rewrite {1}/variation/=.
rewrite size_rcons.
rewrite big_nat_recr//=.
rewrite [X in _ + X](_ : _ = 0) ?addr0.
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

Lemma variation_recl {R : numDomainType} a b (f : R -> R) x s :
  variation a b f (x :: s) = `|f x - f a| + variation x b f s.
Proof. by rewrite /variation/= big_nat_recl. Qed.

Lemma variation_undup {R : realType} f (a b : R) (ab : a < b) s :
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

(* b0 and b1 is just default values of nth in sum *)
Lemma variation_any_ub {R : numDomainType} a b0 b1 f (s : seq R) :
  variation a b0 f s = variation a b1 f s.
Proof.
elim: s a => //.
  move=> a.
  by rewrite !variation_nil.
move=> s0 s1 IH a.
by rewrite !variation_recl IH.
Qed.

Lemma variation_behead {R : numDomainType} a b s (f : R -> R) :
  variation (nth b s 0) b f (behead s) <= variation a b f s.
Proof.
case: s => [|s0 s1]/=.
  by rewrite !variation_nil.
by rewrite /variation/= big_nat_recl//= lerDr.
Qed.

Lemma variation_nth {R : realDomainType} a b (f : R -> R) s : a < b ->
  itv_partition a b s ->
  forall k, (k.+2 <= size s)%N ->
  variation a (nth b s k) f (itv_partitionL s (nth b s k)) <= variation a b f s.
Proof.
move=> ab abs k ks.
rewrite [in leRHS](@in_itv_partition _ _ (nth b s k) s).
  exact: itv_partition_sorted abs.
  apply/(nthP b).
  exists k => //.
  by rewrite (leq_trans _ ks).
rewrite (@variation_cat _ (nth b s k))//.
- apply/ltW.
  exact: (itv_partition_gt_lb _ abs).
- apply: (@itv_partition_nth_le _ _ a _ _ k.+1) => //.
  by rewrite (leq_trans ks).
- apply: itv_partitionLP (abs).
    exact: (itv_partition_gt_lb _ abs).
  exact: (itv_partition_lt_ub abs).
- apply: itv_partitionRP (abs).
    exact: (itv_partition_gt_lb _ abs).
  exact: (itv_partition_lt_ub abs).
- by rewrite lerDl variation_ge0.
Qed.

Lemma filter_iota d {T : orderType d} (a b : T) s : (a < b)%O ->
  itv_partition a b s ->
  forall k, (k < size s)%N ->
  [seq x <- s | x < nth b s k]%O = take k s.
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
rewrite ifT.
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

Lemma variation_nth_nth {R : realDomainType} (a b : R) f s : a < b ->
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
  rewrite (@filter_iota _ _ a)//.
    by rewrite (leq_trans _ ks).
  rewrite (@filter_iota _ _ a)//.
    by rewrite (leq_trans _ ks)// ltnW.
  rewrite (take_nth b) -?cats1//.
  by rewrite (leq_trans _ ks)// ltnW.
rewrite H1.
rewrite -cats1.
rewrite (@variation_cat _ (nth b s k))//.
  apply/ltW.
  by apply: (itv_partition_gt_lb _ abs).
  by apply/ltW.
  apply: itv_partitionLP (abs).
  exact: (itv_partition_gt_lb _ abs).
  apply: (itv_partition_lt_ub abs) => //.
  by rewrite (leq_trans _ ks).
  rewrite /itv_partition/=.
  split => //.
  by rewrite H.
by rewrite lerDl// variation_ge0.
Qed.

Lemma sorted_variation_subseq {R : realDomainType} a b (f : R -> R) s t :
  sorted <=%R s -> sorted <=%R t ->
  subseq s t ->
  variation a b f s <= variation a b f t.
Proof.
elim: s a t.
- by move=> ? ? _; rewrite variation_nil variation_ge0.
move=> + + + + t.
elim: t => // t0 t1 IHt s0 s1 IHs a0 /= ps pt.
have [s0t0 s1st1|s0t0 st1] := eqVneq s0 t0.
  rewrite s0t0 2!variation_recl lerD2l IHs//.
  + exact: path_sorted ps.
  + exact: path_sorted pt.
rewrite (@le_trans _ _ (variation a0 b f t1))//.
  apply: IHt => //.
  exact: path_sorted pt.
exact: le_variation.
Qed.

Lemma in_variation_merge1 {R : realDomainType} a b (f : R -> R) s x : a < b -> itv_partition a b s ->
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
  rewrite ih//.
    apply: itv_partition_size_neq0 s0bs1.
    move: xs1.
    rewrite -index_mem.
    exact: leq_trans.
  by rewrite variation_recl.
case: abs => /= /andP[as0 s0s1 _].
move/order_path_min : s0s1 => /(_ lt_trans)/allP/(_ _ xs1).
by rewrite ltNge s0x.
Qed.

End variation_lemmas.

Section variation_flatten_sum.

Lemma variation_cat_last {R : realDomainType} a b f (s t : seq R) :
  variation a b f (s ++ t) =
  variation a b f s + variation (last a s) b f t.
Proof.
elim: s a.
  by move=> ?; rewrite variation_nil add0r.
by move=> ? ? IH ?; rewrite !variation_recl IH addrA.
Qed.

Context {R : realType}.
Implicit Types (a b c : R) (f : R -> R).

Lemma variation_flatten_sum a b f (ss : seq (seq R)) :
  all (fun s => s != [::]) ss ->
  (variation a b f (flatten ss) =
  \sum_(i < size ss)
    variation
     (nth b [seq last b s | s <- [:: a] :: ss] i)
     (nth b [seq last b s | s <- ss] i)
     f
     (nth [::] ss i)).
Proof.
elim: ss a.
  move=> ?.
  by rewrite variation_nil big_ord0.
move=> s.
case => //.
  rewrite /= => IH a.
  rewrite andbT => s0.
  (* rewrite big_ord1. *)
  rewrite big_ord_recl big_ord0/= addr0 cats0.
  exact: variation_any_ub.
move=> s' ss IH a/=.
move=> /andP[s0 /andP[s'0 ss0]].
have last_s : last a s = last b s.
  by apply: set_last_default; case: s s0.
have s'ssNnil : flatten (s' :: ss) != [::] by exact: cons_flatten_neq_nil.
rewrite big_ord_recl/=.
  under eq_bigr do rewrite add0n.
rewrite -IH//.
  by rewrite /=; apply/andP.
rewrite variation_cat_last// last_s.
congr +%R => //=.
exact: variation_any_ub.
Qed.

(* NB: used in ene6 *)
Lemma variation_flatten_interleave_split a b f (A B : seq (seq R)) :
  all (fun s => s != [::]) (A ++ B) ->
  variation a b f (flatten (interleave A B)) =
    \sum_(i < minn (size A) (size B))
      variation
        (nth b [seq last b s | s <- [:: a] :: B] i)
        (nth b [seq last b s | s <- A] i)
        f
        (nth [::] A i) +
    \sum_(i < minn (size A) (size B))
      variation
        (nth b [seq last b s | s <- A] i)
        (nth b [seq last b s | s <- B] i)
        f
        (nth [::] B i).
Proof.
rewrite all_cat.
elim: A B a.
  case.
    move=> B a/=.
    by rewrite variation_nil !big_ord0 addr0.
  move=> y B a/=.
  by rewrite variation_nil !big_ord0 addr0.
move=> x A IH.
case => /=.
  move=> a.
  by rewrite variation_nil !big_ord0 addr0.
move=> y B a.
move=> /andP[/andP[x0 A0] /andP[y0 B0]].
rewrite /= !variation_cat_last.
have -> : last a x = last b x by case: x x0.
have -> : last (last b x) y = last b y by case: y y0.
rewrite (IH B (last b y) _) ?minnSS ?A0 ?B0// !big_ord_recl /= addrA addrACA.
by congr (_ + _ + (_ + _)); apply: variation_any_ub.
Qed.

End variation_flatten_sum.

Section variations_lemmas.
Context {R : realDomainType}.

(* TODO: not used *)
Lemma variations_eq0 (a b : R) (f : R -> R) :
  b < a -> variations a b f = set0.
Proof.
move=> ba.
rewrite -subset0 => /= x [s /itv_partition_le].
by rewrite leNgt ba.
Qed.

End variations_lemmas.

Section total_variation_lemmas.

Lemma total_variationP {R : realType} a b (f : R -> R) : (a <= b)%R ->
  total_variation a b f = +oo%E <->
  total_variation a b f \isn't a fin_num.
Proof.
move=> ab; split => [->//|].
rewrite fin_numEn => /orP[|/eqP//].
rewrite -leeNy_eq leNgt => /negP abs.
absurd.
apply: abs.
by rewrite (lt_le_trans _ (total_variation_ge0 _ _)).
Qed.

Lemma total_variation_sum {R : realType} (a b : R) (f : R -> R) (s : seq R) :
  itv_partition a b s ->
  total_variation a b f =
    \sum_(i < size s)
      total_variation (nth a (a :: s) i) (nth b s i) f.
Proof.
move: a; elim: s => [a'|x s IH a' ps].
  move/itv_partition_nil ->.
  by rewrite total_variationxx big_ord0.
rewrite big_ord_recl/=.
have pxs := itv_partition_cons ps.
have a'x : a' <= x by apply: ltW; have [/andP[]] := ps.
have xb : x <= b by exact: (@itv_partition_nth_le _ _ _ _ s 0).
rewrite (total_variationD f a'x xb).
congr +%E; rewrite (IH x)//.
by apply: eq_bigr => /= i _; rewrite add0n (set_nth_default x a')// ltnW//= ltnS.
Qed.

Lemma not_bounded_variationP {R : realType} (a b : R) (f : R -> R) :
  (a <= b)%R ->
  ~ bounded_variation a b f <-> total_variation a b f = +oo%E.
Proof.
move=> ab.
split=> [abf|abf].
  apply/total_variationP => //.
  contra: abf.
  by move/bounded_variationP; apply.
move/bounded_variationP => /(_ ab).
apply/negP.
by apply/total_variationP.
Qed.

Lemma bounded_variationS {R : numDomainType} [a c b d : R] [f : R -> R] :
  c <= d -> a <= c -> d <= b ->
  bounded_variation a b f -> bounded_variation c d f.
Proof.
move=> cd ac db abf.
suff: bounded_variation a d f.
  by apply: bounded_variationr.
apply: bounded_variationl abf => //.
by rewrite (le_trans ac).
Qed.

Lemma bounded_variation_total_nondecreasing {R : realType} (a b : R) (f : R -> R) :
  bounded_variation a b f ->
  let H := fun x => fine (total_variation a ^~ f x) in
  {in `[a, b] &, nondecreasing_fun H}.
Proof.
move=> bvf H x y xab yab xy.
have axyf := @total_variation_nondecreasing R a b f _ _ xab yab xy.
rewrite /H fine_le//.
- apply/bounded_variationP => //.
    by rewrite (itvP xab).
  by move: bvf; apply: bounded_variationl; rewrite (itvP xab).
- apply/bounded_variationP => //.
    by rewrite (itvP yab).
  by move: bvf; apply: bounded_variationl; rewrite (itvP yab).
Qed.

Lemma total_variation_ge_sub {R : realType} (A : set R) (f : R -> R) :
  bounded_set A ->
  forall x y, A x -> A y ->
  (`|f x - f y|%:E <= total_variation (inf A) (sup A) f)%E.
Proof.
move=> boundA x y.
wlog : x y / x < y.
  move=> wlg Ax Ay.
  have [xy|yx|xy]:= ltgtP x y.
  - exact: wlg.
  - by rewrite distrC wlg.
  - rewrite xy subrr normr0 total_variation_ge0//.
    by rewrite has_bound_inf_sup//; [exact: bounded_has_lbound|
                                     exact: bounded_has_ubound].
move=> xy Ax Ay.
have infAx : inf A <= x by apply: ge_inf => //; exact: bounded_has_lbound.
have ysupA : y <= sup A by apply: ub_le_sup => //; exact: bounded_has_ubound.
apply: le_ereal_sup_tmp.
exists (`|f x - f (inf A)| + `|f y - f x| + `|f (sup A) - f y|)%:E.
  eexists; last reflexivity.
  move: infAx; rewrite le_eqVlt => /predU1P[<-|infA].
  - rewrite subrr normr0 add0r.
    move: ysupA; rewrite le_eqVlt => /predU1P[->|ysupA].
    + rewrite subrr normr0 addr0.
      exists [:: sup A].
        rewrite /itv_partition/=.
        split => //; rewrite andbT.
        rewrite (@le_lt_trans _ _ x)//.
          by rewrite ge_inf//; exact: bounded_has_lbound.
        rewrite (@lt_le_trans _ _ y)//.
        by rewrite ub_le_sup//; exact: bounded_has_ubound.
      by rewrite !variation_recl variation_nil addr0.
    + exists [:: y; sup A].
        rewrite /itv_partition/=.
        split => //; rewrite ysupA !andbT.
        rewrite (@le_lt_trans _ _ x)//.
        by rewrite ge_inf//; exact: bounded_has_lbound.
      by rewrite !variation_recl variation_nil addr0.
  - move: ysupA; rewrite le_eqVlt => /predU1P[->|ysupA].
    + rewrite subrr normr0 addr0.
      exists [:: x; sup A].
        rewrite /itv_partition/=.
        split => //; rewrite infA andbT/=.
        rewrite (@lt_le_trans _ _ y)//.
        by rewrite ub_le_sup//; exact: bounded_has_ubound.
      by rewrite !variation_recl variation_nil addr0.
    + exists [:: x; y; sup A].
        rewrite /itv_partition/=.
        by split => //; rewrite infA andbT xy/= ysupA.
      by rewrite !variation_recl variation_nil addr0 addrA.
rewrite [in leLHS]distrC.
by rewrite !EFinD addeC addeA leeDr// adde_ge0.
Qed.

End total_variation_lemmas.

Section odd_even_reindexing.
(* used in
   total_variation_interleave_split
   and in
   sum_oscillation_le_total_variation *)

Lemma ltn_div2 n j : (j < n.+1.*2)%N -> (j./2 < n.+1)%N.
Proof. by move=> jm; rewrite ltn_half_double. Qed.

Lemma ltn_mul2 n j : (j < n.+1)%N -> (j.*2 < n.+1.*2)%N .
Proof. by move=> jm; rewrite ltn_double. Qed.

Lemma bigop_mul2_even {T : numDomainType} n (f : nat -> T) :
  \sum_(0 <= i < n) f i.*2 =
  \sum_(0 <= i < n.*2 | ~~ odd i) f i.
Proof.
elim: n => [|n ih].
  by rewrite double0 !big_mkord !big_ord0.
rewrite big_nat_recr//= ih.
rewrite [in RHS]doubleS.
rewrite [in RHS]big_mkcond/=.
rewrite !big_mkord/=.
rewrite 2![in RHS]big_ord_recr//=.
rewrite -big_mkcond/= !negbK -addrA; congr +%R.
by rewrite odd_double/= addr0.
Qed.

Lemma bigop_mul2_odd {T : numDomainType} n (f : nat -> T) :
  \sum_(0 <= i < n) f i.*2.+1 =
  \sum_(0 <= i < n.*2 | odd i) f i.
Proof.
elim: n => [|n ih].
  by rewrite double0 !big_mkord !big_ord0.
rewrite big_nat_recr//= ih.
rewrite [in RHS]doubleS.
rewrite [in RHS]big_mkcond/=.
rewrite !big_mkord/=.
rewrite 2![in RHS]big_ord_recr//=.
rewrite -big_mkcond/= -addrA; congr +%R.
by rewrite odd_double/= add0r.
Qed.

Lemma esum_mul2_even {T : pzSemiRingType} n (f : nat -> \bar T) :
  \sum_(0 <= i < n) f i.*2 =
  \sum_(0 <= i < n.*2 | ~~ odd i) f i.
Proof.
elim: n => [|n ih].
  by rewrite double0 !big_mkord !big_ord0.
rewrite big_nat_recr//= ih.
rewrite [in RHS]doubleS.
rewrite [in RHS]big_mkcond/=.
rewrite !big_mkord/=.
rewrite 2![in RHS]big_ord_recr//=.
rewrite -big_mkcond/= !negbK -addrA; congr +%R.
by rewrite odd_double/= addr0.
Qed.

Lemma esum_mul2_odd {T : pzSemiRingType} n (f : nat -> \bar T) :
  \sum_(0 <= i < n) f i.*2.+1 =
  \sum_(0 <= i < n.*2 | odd i) f i.
Proof.
elim: n => [|n ih].
  by rewrite double0 !big_mkord !big_ord0.
rewrite big_nat_recr//= ih.
rewrite [in RHS]doubleS.
rewrite [in RHS]big_mkcond/=.
rewrite !big_mkord/=.
rewrite 2![in RHS]big_ord_recr//=.
rewrite -big_mkcond/= -addrA; congr +%R.
by rewrite odd_double/= add0r.
Qed.

End odd_even_reindexing.

Section total_variation_sum.
Context {R : realType}.
Variables (a b : R) (f : R -> R).

Lemma total_variation_interleave_split (A B : seq R) (d0 d1 : R) :
  a <= b ->
  itv_partition a b (interleave A B) ->
  total_variation a b f =
   \sum_(i < minn (size A) (size B))
       total_variation (nth d0 (a :: B) i) (nth d1 A i) f +
   \sum_(i < minn (size A) (size B))
       total_variation (nth d1 A i) (nth d0 B i) f.
Proof.
move=> ab pAB.
rewrite (total_variation_sum f pAB).
rewrite size_interleave.
set n := minn (size A) (size B).
rewrite -(big_mkord xpredT
 (fun i => total_variation (nth a (a :: interleave A B) i) (nth b (interleave A B) i) f)).
rewrite [LHS](bigID [pred n | ~~ odd n] xpredT)//=.
congr +%E.
  rewrite -(esum_mul2_even _
 (fun i => total_variation (nth a (a :: interleave A B) i) (nth b (interleave A B) i) f)).
  rewrite big_mkord.
  apply: eq_bigr => i _.
  have i2AB : (i.*2 < size (interleave A B))%N.
    rewrite size_interleave -/n; case: i; case => /=.
      by rewrite double0 double_gt0.
    move=> i.
    case: n => // n.
    by move/ltn_mul2; rewrite -!mul2n.
  congr total_variation.
  case: i i2AB; case => //= i i1ltn i12AB.
    rewrite nth_interleaveE ifT//=.
      by apply: leq_ltn_trans i12AB; rewrite doubleS.
    rewrite odd_double/=.
    rewrite uphalf_double.
    apply: set_nth_default.
    apply: (@ltn_leq_trans n).
      exact: (ltn_trans _ i1ltn).
    by rewrite /n/minn; case: ifP => //; apply: ltnW.
  rewrite nth_interleaveE ifT//.
  rewrite odd_double doubleK.
  apply: set_nth_default.
  apply: (@ltn_leq_trans n).
    exact: (ltn_ord i).
  rewrite /n/minn; case: ifP => //.
  by move/negP/negP; rewrite -leqNgt.
have : n = minn (size A) (size B) by [].
case: n.
  by rewrite double0 big_mkord !big_ord0.
move=> n nE.
rewrite big_mkcond/=.
under [LHS]eq_bigr do rewrite negbK.
rewrite -big_mkcond/=.
rewrite -esum_mul2_odd.
rewrite big_mkord.
apply: eq_bigr => i _/=.
rewrite !nth_interleaveE size_interleave oddS odd_double/=.
congr total_variation.
  rewrite ifT.
    rewrite -nE -!mul2n ltn_pmul2l//.
  rewrite doubleK.
  apply: set_nth_default.
  apply: (leq_trans (ltn_ord i)).
  rewrite -ltnS nE /minn; case: ifP => //.
  by move/negP/negP; rewrite -leqNgt.
case: ifP.
  move=> H.
  rewrite uphalf_double.
  apply: set_nth_default.
  apply: (leq_trans (ltn_ord i)).
  rewrite -ltnS nE /minn; case: ifP => //.
  rewrite -ltnS.
  by move/(leq_trans _); apply.
move/negP/negP; rewrite -leqNgt -nE.
rewrite ltnS.
rewrite ltn_double.
by have := ltn_ord i; rewrite ltnNge => /negP.
Qed.

End total_variation_sum.

Section bounded_variation_lemmas.

Lemma sup_not_bounded_variation {R : realType} (A : set R) f :
  bounded_set A ->
  ereal_sup [set (EFin \o f) x | x in A] = +oo%E ->
  ~ bounded_variation (inf A) (sup A) f.
Proof.
move=> boundA.
have [->|/set0P [r Ar] fAy] := eqVneq A set0.
  by rewrite image_set0 ereal_sup0.
move/bounded_variationP.
rewrite has_bound_inf_sup//; [exact: bounded_has_lbound|
                              exact: bounded_has_ubound|].
move=> /(_ isT).
set M := total_variation _ _ _.
move=> Mfin.
suff : (ereal_sup ((EFin \o f) @` A) <= (f r)%:E + (M + 1))%E.
  by rewrite fAy leNgt ltey negbK -(fineK Mfin).
suff: ((EFin \o f) @` A) `<=` `]-oo, (f r)%:E + (M + 1)%E[.
  move/ereal_sup_le => /le_trans; apply.
  by apply: ge_ereal_sup => z/= /itvP ->.
move=> _ /= [s As <-].
rewrite in_itv/= -(fineK Mfin) lte_fin//.
rewrite (@le_lt_trans _ _ (f r + `|f s - f r|))//.
  by rewrite -lerBlDl ler_norm.
rewrite ltrD2l.
rewrite -ltrBlDr.
rewrite -lte_fin fineK//.
rewrite EFinB.
rewrite (@lt_le_trans _ _ `|f s - f r|%:E)//.
   by rewrite lteBlDr// lteDl.
by rewrite total_variation_ge_sub.
Qed.

Lemma inf_not_bounded_variation {R : realType} (A : set R) f :
  bounded_set A ->
  ereal_inf [set (EFin \o f) x | x in A] = -oo%E ->
  ~ bounded_variation (inf A) (sup A) f.
Proof.
move=> boudnA.
rewrite /ereal_inf => /(congr1 (fun x => - x)%E).
rewrite oppeK/=.
rewrite image_comp.
move/sup_not_bounded_variation => fA.
by move/bounded_variationN; exact: fA.
Qed.

End bounded_variation_lemmas.
