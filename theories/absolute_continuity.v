From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop .
Require Import signed reals ereal topology normedtype sequences real_interval.
Require Import esum measure lebesgue_measure numfun lebesgue_integral.

(**md**************************************************************************)
(* # Absolute Continuity                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.


Section Absolute_Continuous.
Context (R : realType).

(* this would be used in abs_cont_bounded_variation *)
Lemma itv_partition_undup_merge (a b : R) (s t : seq R) :
itv_partition a b s -> itv_partition a b t ->
itv_partition a b (undup (merge <%R s t)).
Proof.
Admitted.

Definition abs_cont (a b : R) (f : R -> R) := forall e : {posnum R},
  exists d : {posnum R}, forall (I : finType) (B : I -> R * R),
    (forall i, (B i).1 <= (B i).2 /\ `[(B i).1, (B i).2] `<=` `[a, b]) /\
      trivIset setT (fun i => `[(B i).1, (B i).2]%classic) /\
    \sum_(k in I) ((B k).2 - (B k).1) < d%:num ->
    \sum_(k in I) (f (B k).2 - f ((B k).1)) < e%:num.

Lemma abs_cont_bounded_variation (a b : R) (f : R -> R) :
abs_cont a b f -> bounded_variation a b f.
Proof.
Admitted.

End Absolute_Continuous.

(* ========================================================================== *)

Section extend.
Context {R : realType}.
Implicit Type (f : R -> R).

Definition extend f (x : \bar R) : \bar R :=
match x with
| r%:E => (f r)%:E
| +oo%E => lim ((f r)%:E @[r --> +oo])
| -oo%E => lim ((f r)%:E @[r --> -oo])
end.

End extend.

Section einterval_partition.
Context {R : realType}.
Implicit Type (a b : \bar R) (s : seq (\bar R)).

Local Open Scope ereal_scope.

(** a :: s is a partition of the interval [a, b] *)
Definition eitv_partition a b s := [/\ path lte a s & last a s == b].

Lemma eitv_partition_nil a b : eitv_partition a b [::] -> a = b.
Proof. by move=> [_ /eqP <-]. Qed.

Lemma eitv_partition_cons a b x s :
  eitv_partition a b (x :: s) -> eitv_partition x b s.
Proof. by rewrite /eitv_partition/= => -[/andP[]]. Qed.

Lemma eitv_partition1 a b : a < b -> eitv_partition a b [:: b].
Proof. by rewrite /eitv_partition /= => ->. Qed.

Lemma eitv_partition_size_neq0 a b s :
  (size s > 0)%N -> eitv_partition a b s -> a < b.
Proof.
elim: s a => // x [_ a _|h t ih a _]; rewrite /eitv_partition /=.
  by rewrite andbT => -[ax /eqP <-].
move=> [] /andP[ax /andP[xh] ht /eqP tb].
by rewrite (lt_trans ax)// ih// /eitv_partition /= xh/= tb.
Qed.

Lemma eitv_partitionxx a s : eitv_partition a a s -> s = [::].
Proof.
case: s => //= h t [/= /andP[ah /lt_path_min/allP ht] /eqP hta].
suff : h < a by move/lt_trans => /(_ _ ah); rewrite ltxx.
apply/ht; rewrite -hta.
by have := mem_last h t; rewrite inE hta lt_eqF.
Qed.

Lemma eitv_partition_le a b s : eitv_partition a b s -> a <= b.
Proof.
case: s => [/eitv_partition_nil ->//|h t /eitv_partition_size_neq0 - /(_ _)/ltW].
exact.
Qed.

Lemma eitv_partition_cat a b c s t :
  eitv_partition a b s -> eitv_partition b c t -> eitv_partition a c (s ++ t).
Proof.
rewrite /eitv_partition => -[sa /eqP asb] [bt btc].
by rewrite cat_path// sa /= last_cat asb.
Qed.

Lemma eitv_partition_nth_size def a b s : eitv_partition a b s ->
  nth def (a :: s) (size s) = b.
Proof.
by elim: s a => [a/= /eitv_partition_nil//|y t ih a /= /eitv_partition_cons/ih].
Qed.

Lemma eitv_partition_nth_ge a b s m : (m < (size s).+1)%N ->
  eitv_partition a b s -> a <= nth b (a :: s) m.
Proof.
elim: m s a b => [s a b _//|n ih [//|h t] a b].
rewrite ltnS => nh [/= /andP[ah ht] lb].
by rewrite (le_trans (ltW ah))// ih.
Qed.

Lemma eitv_partition_nth_le a b s m : (m < (size s).+1)%N ->
  eitv_partition a b s -> nth b (a :: s) m <= b.
Proof.
elim: m s a => [s a _|n ih]; first exact: eitv_partition_le.
by move=> [//|a h t /= nt] H; rewrite ih//; exact: eitv_partition_cons H.
Qed.

Lemma nondecreasing_fun_eitv_partition a b f s :
  {in `[a, b] &, nondecreasing_fun f} -> eitv_partition a b s ->
  let F : nat -> \bar R := f \o nth b (a :: s) in
  forall k, (k < size s)%N -> F k <= F k.+1.
Proof.
move=> ndf abs F k ks.
have [_] := nondecreasing_seqP F; apply => m n mn; rewrite /F/=.
have [ms|ms] := ltnP m (size s).+1; last first.
  rewrite nth_default//.
  have [|ns] := ltnP n (size s).+1; last by rewrite nth_default.
  by move=> /(leq_ltn_trans mn); rewrite ltnS leqNgt ms.
have [ns|ns] := ltnP n (size s).+1; last first.
  rewrite [in leRHS]nth_default//=; apply/ndf/eitv_partition_nth_le => //.
    by rewrite in_itv/= eitv_partition_nth_le// andbT eitv_partition_nth_ge.
  by rewrite in_itv/= lexx andbT; exact: (eitv_partition_le abs).
move: abs; rewrite /eitv_partition => -[] sa sab.
move: mn; rewrite leq_eqVlt => /predU1P[->//|mn].
apply/ndf/ltW/sorted_ltn_nth => //=; last exact: lt_trans.
  by rewrite in_itv/= eitv_partition_nth_le// andbT eitv_partition_nth_ge.
by rewrite in_itv/= eitv_partition_nth_le// andbT eitv_partition_nth_ge.
Qed.

Lemma nondecreasing_efunN a b (f : \bar R -> \bar R) :
  {in `[a, b] &, nondecreasing_fun f} <->
  {in `[a, b] &, nonincreasing_fun (\- f)}.
Proof.
split=> [h m n mab nab mn|h m n mab nab mn]; first by rewrite leeN2 h.
by rewrite -leeN2 h.
Qed.

Lemma nonincreasing_efunN a b (f : \bar R -> \bar R) :
  {in `[a, b] &, nonincreasing_fun f} <->
  {in `[a, b] &, nondecreasing_fun (\- f)}.
Proof.
apply: iff_sym; apply: (iff_trans (nondecreasing_efunN a b (\- f))).
rewrite [in X in _ <-> X](_ : f = \- (\- f))//.
by apply/funext => x /=; rewrite oppeK.
Qed.

Lemma nonincreasing_fun_eitv_partition a b f s :
  {in `[a, b] &, nonincreasing_fun f} -> eitv_partition a b s ->
  let F : nat -> \bar R := f \o nth b (a :: s) in
  forall k, (k < size s)%N -> F k.+1 <= F k.
Proof.
move/nonincreasing_efunN => ndNf abs F k ks; rewrite -leeN2.
exact: (nondecreasing_fun_eitv_partition ndNf abs).
Qed.

(** given a partition of [a, b] and c, returns a partition of [a, c] *)
Definition eitv_partitionL s c := rcons [seq x <- s | x < c] c.

Lemma eitv_partitionLP a b c s : a < c -> c < b -> eitv_partition a b s ->
  eitv_partition a c (eitv_partitionL s c).
Proof.
move=> ac bc [] al /eqP htb; split.
  rewrite /eitv_partitionL rcons_path/=; apply/andP; split.
    by apply: path_filter => //; exact: lt_trans.
  exact: (last_filterP [pred x | x < c]).
by rewrite /eitv_partitionL last_rcons.
Qed.

(** given a partition of [a, b] and c, returns a partition of [c, b] *)
Definition eitv_partitionR s c := [seq x <- s | c < x].

Lemma eitv_partitionRP a b c s : a < c -> c < b -> eitv_partition a b s ->
  eitv_partition c b (eitv_partitionR s c).
Proof.
move=> ac cb [] sa /eqP alb; rewrite /eitv_partition; split.
  move: sa; rewrite lt_path_sortedE => /andP[allas ss].
  rewrite lt_path_sortedE filter_all/=.
  by apply: sorted_filter => //; exact: lt_trans.
exact/eqP/(path_lt_last_filter ac).
Qed.

Lemma in_eitv_partition c s : sorted <%O s -> c \in s ->
  s = eitv_partitionL s c ++ eitv_partitionR s c.
Proof.
elim: s c => // h t ih c /= ht.
rewrite inE => /predU1P[->{c}/=|ct].
  rewrite ltxx /eitv_partitionL /= ltxx /eitv_partitionR/= path_lt_filter0//=.
  by rewrite path_lt_filterT.
rewrite /eitv_partitionL/=; case: ifPn => [hc|].
  by rewrite ltNge (ltW hc)/= /= [in LHS](ih _ _ ct)//; exact: path_sorted ht.
rewrite -leNgt le_eqVlt => /predU1P[ch|ch].
  by rewrite ch ltxx path_lt_filter0//= /eitv_partitionR path_lt_filterT.
move: ht; rewrite lt_path_sortedE => /andP[/allP/(_ _ ct)].
by move=> /lt_trans-/(_ _ ch); rewrite ltxx.
Qed.

Lemma notin_eitv_partition c s : sorted <%O s -> c \notin s ->
  s = [seq x <- s | x < c] ++ eitv_partitionR s c.
Proof.
elim: s c => // h t ih c /= ht.
rewrite inE negb_or => /andP[]; rewrite neq_lt => /orP[ch|ch] ct.
  rewrite ch ltNge (ltW ch)/= path_lt_filter0/= /eitv_partitionR; last first.
    exact: path_lt_head ht.
  by rewrite path_lt_filterT//; exact: path_lt_head ht.
by rewrite ch/= ltNge (ltW ch)/= -ih//; exact: path_sorted ht.
Qed.

Lemma eitv_partition_rev a b s : eitv_partition a b s ->
  eitv_partition (- b) (- a) (rev (belast (- a) (map -%E s))).
Proof.
move=> [sa /eqP alb]; split.
  rewrite (_ : - b = last (- a) (map -%E s)); last by rewrite last_map alb.
  rewrite rev_path// path_map.
  by apply: sub_path sa => x y xy/=; rewrite lteN2.
case: s sa alb => [_ <-//|h t] /= /andP[ah ht] <-{b}.
by rewrite rev_cons last_rcons.
Qed.

End einterval_partition.

Section evariation.
Context {R : realType}.
Implicit Types (a b : \bar R) (f g : \bar R -> \bar R).

Local Open Scope ereal_scope.

Definition evariation a b f s := let F := f \o nth b (a :: s) in
  \sum_(0 <= n < size s) `|F n.+1 - F n|.

Lemma evariation_zip a b f s : eitv_partition a b s ->
  evariation a b f s = \sum_(x <- zip s (a :: s)) `|f x.1 - f x.2|.
Proof.
elim: s a b => // [a b|h t ih a b].
  by rewrite /eitv_partition /= => -[_ /eqP <-]; rewrite /evariation/= !big_nil.
rewrite /eitv_partition /evariation => -[]/= /andP[ah ht] /eqP htb.
rewrite big_nat_recl//= big_cons/=; congr +%R.
have /ih : eitv_partition h b t by split => //; exact/eqP.
by rewrite /evariation => ->; rewrite !big_seq; apply/eq_bigr => r rt.
Qed.

(* NB: not used yet but should allow for "term-by-term" comparisons *)
Lemma evariation_prev a b f s : eitv_partition a b s ->
  evariation a b f s = \sum_(x <- s) `|f x - f (prev (locked (a :: s)) x)|.
Proof.
move=> [] sa /eqP asb; rewrite /evariation [in LHS]/= (big_nth b) !big_nat.
apply: eq_bigr => i /andP[_ si]; congr (`| _ - f _ |).
rewrite -lock.
rewrite prev_nth inE gt_eqF; last first.
  rewrite -[a]/(nth b (a :: s) 0) -[ltRHS]/(nth b (a :: s) i.+1).
  exact: lt_sorted_ltn_nth.
rewrite orFb mem_nth// index_uniq//.
  by apply: set_nth_default => /=; rewrite ltnS ltnW.
by apply: (sorted_uniq lt_trans) => //; apply: path_sorted sa.
Qed.

Lemma evariation_next a b f s : eitv_partition a b s ->
  evariation a b f s =
  \sum_(x <- belast a s) `|f (next (locked (a :: s)) x) - f x|.
Proof.
move=> [] sa /eqP asb; rewrite /evariation [in LHS]/= (big_nth b) !big_nat.
rewrite size_belast; apply: eq_bigr => i /andP[_ si].
congr (`| f _ - f _ |); last first.
  by rewrite lastI -cats1 nth_cat size_belast// si.
rewrite -lock next_nth.
rewrite {1}lastI mem_rcons inE mem_nth ?size_belast// orbT.
rewrite lastI -cats1 index_cat mem_nth ?size_belast//.
rewrite index_uniq ?size_belast//.
  exact: set_nth_default.
have /lt_sorted_uniq : sorted <%O (a :: s) by [].
by rewrite lastI rcons_uniq => /andP[].
Qed.

Lemma evariation_nil a b f : evariation a b f [::] = 0.
Proof. by rewrite /evariation/= big_nil. Qed.

Lemma evariation_ge0 a b f s : 0 <= evariation a b f s.
Proof. exact/sume_ge0. Qed.

(*

Lemma evariation_

Lemma evariationN a b f s : evariation a b (\- f) s = evariation a b f s.
Proof.
case h : (evariation a b f s).
- rewrite /evariation; apply: eq_bigr => k _ /=.
rewrite -oppeD; first rewrite abseN //.
Qed.

Lemma variation_le a b f g s :
  variation a b (f \+ g)%R s <= variation a b f s + variation a b g s.
Proof.
rewrite [in leRHS]/variation -big_split/=.
apply: ler_sum => k _; apply: le_trans; last exact: ler_norm_add.
by rewrite /= addrACA addrA opprD addrA.
Qed.

Lemma nondecreasing_variation a b f s : {in `[a, b] &, nondecreasing_fun f} ->
  itv_partition a b s -> variation a b f s = f b - f a.
Proof.
move=> ndf abs; rewrite /variation; set F : nat -> R := f \o nth _ (a :: s).
transitivity (\sum_(0 <= n < size s) (F n.+1 - F n)).
  rewrite !big_nat; apply: eq_bigr => k; rewrite leq0n/= => ks.
  by rewrite ger0_norm// subr_ge0; exact: nondecreasing_fun_itv_partition.
by rewrite telescope_sumr// /F/= (itv_partition_nth_size _ abs).
Qed.

Lemma nonincreasing_variation a b f s : {in `[a, b] &, nonincreasing_fun f} ->
  itv_partition a b s -> variation a b f s = f a - f b.
Proof.
move=> /nonincreasing_funN ndNf abs; have := nondecreasing_variation ndNf abs.
by rewrite opprK addrC => <-; rewrite variationN.
Qed.

Lemma variationD a b c f s t : a <= c -> c <= b ->
  itv_partition a c s -> itv_partition c b t ->
  variation a c f s + variation c b f t = variation a b f (s ++ t).
Proof.
rewrite le_eqVlt => /predU1P[<-{c} cb|ac].
  by move=> /itv_partitionxx ->; rewrite variation_nil add0r.
rewrite le_eqVlt => /predU1P[<-{b}|cb].
  by move=> ? /itv_partitionxx ->; rewrite variation_nil addr0 cats0.
move=> acs cbt; rewrite /variation /= [in RHS]/index_iota subn0 size_cat.
rewrite iotaD add0n big_cat/= -[in X in _ = X + _](subn0 (size s)); congr +%R.
  rewrite -/(index_iota 0 (size s)) 2!big_nat.
  apply: eq_bigr => k /[!leq0n] /= ks.
  rewrite nth_cat ks -cat_cons nth_cat /= ltnS (ltnW ks).
  by rewrite !(set_nth_default b c)//= ltnS ltnW.
rewrite -[in RHS](addnK (size s) (size t)).
rewrite -/(index_iota (size s) (size t + size s)).
rewrite -{1}[in RHS](add0n (size s)) big_addn addnK 2!big_nat; apply: eq_bigr.
move=> k /[!leq0n]/= kt.
rewrite nth_cat {1}(addnC k) -ltn_subRL subnn ltn0 addnK.
case: k kt => [t0 /=|k kt].
  rewrite add0n -cat_cons nth_cat/= ltnS leqnn -last_nth.
  by case: acs => _ /eqP ->.
rewrite addSnnS (addnC k) -cat_cons nth_cat/= -ltn_subRL subnn ltn0.
by rewrite -(addnC k) addnK.
Qed.

(* NB: this is the only lemma that uses variation_zip *)
Lemma variation_itv_partitionLR a b c f s : a < c -> c < b ->
  itv_partition a b s ->
  variation a b f s <= variation a b f (itv_partitionL s c ++ itv_partitionR s c).
Proof.
move=> ac bc abs; have [cl|cl] := boolP (c \in s).
  by rewrite -in_itv_partition//; case: abs => /path_sorted.
rewrite /itv_partitionL [in leLHS](notin_itv_partition _ cl)//; last first.
  by apply: path_sorted; case: abs => + _; exact.
rewrite -notin_itv_partition//; last first.
  by apply: path_sorted; case: abs => /= + _; exact.
rewrite !variation_zip//; last first.
  by apply: itv_partition_cat;
    [exact: (itv_partitionLP _ bc)|exact: (itv_partitionRP ac)].
rewrite [in leLHS](notin_itv_partition _ cl); last first.
  by apply: path_sorted; case: abs => + _; exact.
set L := [seq x <- s | x < c].
rewrite -cats1 -catA.
move: L => L.
set B := itv_partitionR s c.
move: B => B.
elim/last_ind : L => [|L0 L1 _].
  rewrite !cat0s /=; case: B => [|B0 B1].
    by rewrite big_nil big_cons/= big_nil addr0.
  rewrite !big_cons/= addrA lerD// [leRHS]addrC.
  by rewrite (le_trans _ (ler_normD _ _))// addrA subrK.
rewrite -cats1.
rewrite (_ : a :: _ ++ B = (a :: L0) ++ [:: L1] ++ B)//; last first.
  by rewrite -!catA -cat_cons.
rewrite zip_cat; last by rewrite cats1 size_rcons.
rewrite (_ : a :: _ ++ _ ++ B = (a :: L0) ++ [:: L1] ++ [:: c] ++ B); last first.
  by rewrite -!catA -cat_cons.
rewrite zip_cat; last by rewrite cats1 size_rcons.
rewrite !big_cat lerD//.
case: B => [|B0 B1].
  by rewrite /= big_nil big_cons big_nil addr0.
rewrite -cat1s zip_cat// catA.
rewrite (_ : [:: L1] ++ _ ++ B1 = ([:: L1] ++ [:: c]) ++ [:: B0] ++ B1); last first.
  by rewrite catA.
rewrite zip_cat// !big_cat lerD//= !big_cons !big_nil !addr0/= [leRHS]addrC.
  by rewrite (le_trans _ (ler_normD _ _))// addrA subrK.
Qed.

Lemma le_variation a b f s x : variation a b f s <= variation a b f (x :: s).
Proof.
case: s => [|h t].
  by rewrite variation_nil /variation/= big_nat_recl//= big_nil addr0.
rewrite /variation/= !big_nat_recl//= addrA lerD2r.
by rewrite (le_trans _ (ler_normD _ _))// (addrC (f x - _)) addrA subrK.
Qed.

Lemma variation_opp_rev a b f s : itv_partition a b s ->
  variation a b f s =
  variation (- b) (- a) (f \o -%R) (rev (belast (- a) (map -%R s))).
Proof.
move=> abl; rewrite belast_map /variation /= [LHS]big_nat_rev/= add0n.
rewrite size_rev size_map size_belast 2!big_nat.
apply: eq_bigr => k; rewrite leq0n /= => ks.
rewrite nth_rev ?size_map ?size_belast// [in RHS]distrC.
rewrite (nth_map a); last first.
  by rewrite size_belast ltn_subLR// addSn ltnS leq_addl.
rewrite opprK -rev_rcons nth_rev ?size_rcons ?size_map ?size_belast 1?ltnW//.
rewrite subSn// -map_rcons (nth_map b) ?size_rcons ?size_belast; last first.
  by rewrite ltnS ltn_subLR// addSn ltnS leq_addl.
rewrite opprK nth_rcons size_belast -subSn// subSS.
rewrite (ltn_subLR _ (ltnW ks)) if_same.
case: k => [|k] in ks *.
  rewrite add0n ltnn subn1 (_ : nth b s _ = b); last first.
    case: abl ks => _.
    elim/last_ind : s => // h t _; rewrite last_rcons => /eqP -> _.
    by rewrite nth_rcons size_rcons ltnn eqxx.
  rewrite (_ : nth b (a :: s) _ = nth a (belast a s) (size s).-1)//.
  case: abl ks => _.
  elim/last_ind : s => // h t _; rewrite last_rcons => /eqP -> _.
  rewrite belast_rcons size_rcons/= -rcons_cons nth_rcons/= ltnS leqnn.
  exact: set_nth_default.
rewrite addSn ltnS leq_addl//; congr (`| f _ - f _ |).
  elim/last_ind : s ks {abl} => // h t _; rewrite size_rcons ltnS => kh.
  rewrite belast_rcons nth_rcons subSS ltn_subLR//.
  by rewrite addSn ltnS leq_addl// subSn.
elim/last_ind : s ks {abl} => // h t _; rewrite size_rcons ltnS => kh.
rewrite belast_rcons subSS -rcons_cons nth_rcons /= ltn_subLR//.
rewrite addnS ltnS leq_addl; apply: set_nth_default => //.
by rewrite /= ltnS leq_subLR leq_addl.
Qed.

Lemma variation_rev_opp a b f s : itv_partition (- b) (- a) s ->
  variation a b f (rev (belast b (map -%R s))) =
  variation (- b) (- a) (f \o -%R) s.
Proof.
move=> abs; rewrite [in RHS]variation_opp_rev ?opprK//.
suff: (f \o -%R) \o -%R = f by move=> ->.
by apply/funext=> ? /=; rewrite opprK.
Qed.

Lemma variation_subseq a b f (s t : list R) :
  itv_partition a b s -> itv_partition a b t ->
  subseq s t ->
  variation a b f s <= variation a b f t.
Proof.
elim: t s a => [? ? ? /= _ /eqP ->//|a s IH [|x t] w].
  by rewrite variation_nil // variation_ge0.
move=> /[dup] /itv_partition_cons itvxb /[dup] /itv_partition_le wb itvxt.
move=> /[dup] /itv_partition_cons itvas itvws /=.
have ab : a <= b by exact: (itv_partition_le itvas).
have wa : w < a by case: itvws => /= /andP[].
have waW : w <= a := ltW wa.
case: ifPn => [|] nXA.
  move/eqP : nXA itvxt itvxb => -> itvat itvt /= ta.
  rewrite -[_ :: t]cat1s -[_ :: s]cat1s.
  rewrite -?(@variationD _ _ a)//; [|exact: itv_partition1..].
  by rewrite lerD// IH.
move=> xts; rewrite -[_ :: s]cat1s -(@variationD _ _ a) => //; last first.
  exact: itv_partition1.
have [y [s' s'E]] : exists y s', s = y :: s'.
  by case: {itvas itvws IH} s xts => // y s' ?; exists y, s'.
apply: (@le_trans _ _ (variation w b f s)).
  rewrite IH//.
  case: itvws => /= /andP[_]; rewrite s'E /= => /andP[ay ys' lyb].
  by split => //; rewrite (path_lt_head wa)//= ys' andbT.
by rewrite variationD //; [exact: le_variation | exact: itv_partition1].
Qed.

End variation.

Section bounded_variation.
Context {R : realType}.
Implicit Type (a b : R) (f : R -> R).

Definition variations a b f := [set variation a b f l | l in itv_partition a b].

Lemma variations_variation a b f s : itv_partition a b s ->
  variations a b f (variation a b f s).
Proof. by move=> abs; exists s. Qed.

Lemma variations_neq0 a b f : a < b -> variations a b f !=set0.
Proof.
move=> ab; exists (variation a b f [:: b]); exists [:: b] => //.
exact: itv_partition1.
Qed.

Lemma variationsN a b f : variations a b (\- f) = variations a b f.
Proof.
apply/seteqP; split => [_ [s abs] <-|r [s abs]].
  by rewrite variationN; exact: variations_variation.
by rewrite -variationN => <-; exact: variations_variation.
Qed.

Lemma variationsxx a f : variations a a f = [set 0].
Proof.
apply/seteqP; split => [x [_ /itv_partitionxx ->]|x ->].
  by rewrite /variation big_nil => <-.
by exists [::] => //=; rewrite /variation /= big_nil.
Qed.

Definition bounded_variation a b f := has_ubound (variations a b f).

Notation BV := bounded_variation.

Lemma bounded_variationxx a f : BV a a f.
Proof. by exists 0 => r; rewrite variationsxx => ->. Qed.

Lemma bounded_variationD a b f g : a < b ->
  BV a b f -> BV a b g -> BV a b (f \+ g).
Proof.
move=> ab [r abfr] [s abgs]; exists (r + s) => _ [l abl] <-.
apply: le_trans; first exact: variation_le.
rewrite lerD//.
- by apply: abfr; exact: variations_variation.
- by apply: abgs; exact: variations_variation.
Qed.

Lemma bounded_variationN a b f : BV a b f -> BV a b (\- f).
Proof. by rewrite /bounded_variation variationsN. Qed.

Lemma bounded_variationl a c b f : a <= c -> c <= b -> BV a b f -> BV a c f.
Proof.
rewrite le_eqVlt => /predU1P[<-{c} ? ?|ac]; first exact: bounded_variationxx.
rewrite le_eqVlt => /predU1P[<-{b}//|cb].
move=> [x Hx]; exists x => _ [s acs] <-.
rewrite (@le_trans _ _ (variation a b f (rcons s b)))//; last first.
  apply/Hx/variations_variation; case: acs => sa /eqP asc.
  by rewrite /itv_partition rcons_path last_rcons sa/= asc.
rewrite {2}/variation size_rcons -[leLHS]addr0 big_nat_recr//= lerD//.
rewrite /variation !big_nat ler_sum// => k; rewrite leq0n /= => ks.
rewrite nth_rcons// ks -cats1 -cat_cons nth_cat /= ltnS (ltnW ks).
by rewrite ![in leRHS](set_nth_default c)//= ltnS ltnW.
Qed.

Lemma bounded_variationr a c b f : a <= c -> c <= b -> BV a b f -> BV c b f.
Proof.
rewrite le_eqVlt => /predU1P[<-{c}//|ac].
rewrite le_eqVlt => /predU1P[<-{b} ?|cb]; first exact: bounded_variationxx.
move=> [x Hx]; exists x => _ [s cbs] <-.
rewrite (@le_trans _ _ (variation a b f (c :: s)))//; last first.
  apply/Hx/variations_variation; case: cbs => cs csb.
  by rewrite /itv_partition/= ac/= cs.
by rewrite {2}/variation/= -[leLHS]add0r big_nat_recl//= lerD.
Qed.

Lemma variations_opp a b f :
  variations (- b) (- a) (f \o -%R) = variations a b f.
Proof.
rewrite eqEsubset; split=> [_ [s bas <-]| _ [s abs <-]].
  eexists; last exact: variation_rev_opp.
  by move/itv_partition_rev : bas; rewrite !opprK.
eexists; last by exact/esym/variation_opp_rev.
exact: itv_partition_rev abs.
Qed.

Lemma nondecreasing_bounded_variation a b f :
  {in `[a, b] &, {homo f : x y / x <= y}} -> BV a b f.
Proof.
move=> incf; exists (f b - f a) => ? [l pabl <-]; rewrite le_eqVlt.
by rewrite nondecreasing_variation// eqxx.
Qed.

End bounded_variation.

Section total_variation.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).

Definition total_variation a b f :=
  ereal_sup [set x%:E | x in variations a b f].

Notation BV := bounded_variation.
Notation TV := total_variation.

Lemma total_variationxx a f : TV a a f = 0%E.
Proof. by rewrite /total_variation variationsxx image_set1 ereal_sup1. Qed.

Lemma total_variation_ge a b f : a <= b -> (`|f b - f a|%:E <= TV a b f)%E.
Proof.
rewrite le_eqVlt => /predU1P[<-{b}|ab].
  by rewrite total_variationxx subrr normr0.
apply: ereal_sup_ub => /=; exists (variation a b f [:: b]).
  exact/variations_variation/itv_partition1.
by rewrite /variation/= big_nat_recr//= big_nil add0r.
Qed.

Lemma total_variation_ge0 a b f : a <= b -> (0 <= TV a b f)%E.
Proof. by move=> ab; rewrite (le_trans _ (total_variation_ge _ ab)). Qed.

Lemma bounded_variationP a b f : a <= b -> BV a b f <-> TV a b f \is a fin_num.
Proof.
rewrite le_eqVlt => /predU1P[<-{b}|ab].
  by rewrite total_variationxx; split => // ?; exact: bounded_variationxx.
rewrite ge0_fin_numE; last exact/total_variation_ge0/ltW.
split=> [abf|].
  by rewrite /total_variation ereal_sup_EFin ?ltry//; exact: variations_neq0.
rewrite /total_variation /bounded_variation ltey => /eqP; apply: contra_notP.
by move/hasNub_ereal_sup; apply; exact: variations_neq0.
Qed.

Lemma nondecreasing_total_variation a b f : a <= b ->
  {in `[a, b] &, nondecreasing_fun f} -> TV a b f = (f b - f a)%:E.
Proof.
rewrite le_eqVlt => /predU1P[<-{b} ?|ab ndf].
  by rewrite total_variationxx subrr.
rewrite /total_variation [X in ereal_sup X](_ : _ = [set (f b - f a)%:E]).
  by rewrite ereal_sup1.
apply/seteqP; split => [x/= [s [t abt <-{s} <-{x}]]|x/= ->{x}].
  by rewrite nondecreasing_variation.
exists (variation a b f [:: b]) => //.
  exact/variations_variation/itv_partition1.
by rewrite nondecreasing_variation//; exact: itv_partition1.
Qed.

Lemma total_variationN a b f : TV a b (\- f) = TV a b f.
Proof. by rewrite /TV; rewrite variationsN. Qed.

Lemma total_variation_le a b f g : a <= b ->
  (TV a b (f \+ g)%R <= TV a b f + TV a b g)%E.
Proof.
rewrite le_eqVlt => /predU1P[<-{b}|ab].
  by rewrite !total_variationxx adde0.
have [abf|abf] := pselect (BV a b f); last first.
  rewrite {2}/total_variation hasNub_ereal_sup//; last first.
    exact: variations_neq0.
  rewrite addye ?leey// -ltNye (@lt_le_trans _ _ 0%E)//.
  exact/total_variation_ge0/ltW.
have [abg|abg] := pselect (BV a b g); last first.
  rewrite {3}/total_variation hasNub_ereal_sup//; last first.
    exact: variations_neq0.
  rewrite addey ?leey// -ltNye (@lt_le_trans _ _ 0%E)//.
  exact/total_variation_ge0/ltW.
move: abf abg => [r abfr] [s abgs].
have BVabfg : BV a b (f \+ g).
  by apply: bounded_variationD => //; [exists r|exists s].
apply: ub_ereal_sup => y /= [r' [s' abs <-{r'} <-{y}]].
apply: (@le_trans _ _ (variation a b f s' + variation a b g s')%:E).
  exact: variation_le.
by rewrite EFinD lee_add// ereal_sup_le//;
  (eexists; last exact: lexx); (eexists; last reflexivity);
  exact: variations_variation.
Qed.

Let total_variationD1 a b c f : a <= c -> c <= b ->
  (TV a b f >= TV a c f + TV c b f)%E.
Proof.
rewrite le_eqVlt=> /predU1P[<-{c}|ac]; first by rewrite total_variationxx add0e.
rewrite le_eqVlt=> /predU1P[<-{b}|cb]; first by rewrite total_variationxx adde0.
have [abf|abf] := pselect (BV a b f); last first.
  rewrite {3}/total_variation hasNub_ereal_sup ?leey//.
  by apply: variations_neq0 => //; rewrite (lt_trans ac).
have H s t : itv_partition a c s -> itv_partition c b t ->
    (TV a b f >= (variation a c f s)%:E + (variation c b f t)%:E)%E.
  move=> acs cbt; rewrite -EFinD; apply: ereal_sup_le.
  exists (variation a b f (s ++ t))%:E.
    eexists; last reflexivity.
    by exists (s ++ t) => //; exact: itv_partition_cat acs cbt.
  by rewrite variationD// ltW.
rewrite [leRHS]ereal_sup_EFin//; last first.
  by apply: variations_neq0; rewrite (lt_trans ac).
have acf : BV a c f := bounded_variationl (ltW ac) (ltW cb) abf.
have cbf : BV c b f := bounded_variationr (ltW ac) (ltW cb) abf.
rewrite {1 2}/total_variation ereal_sup_EFin//; last exact: variations_neq0.
rewrite ereal_sup_EFin//; last exact: variations_neq0.
rewrite -EFinD -sup_sumE; last 2 first.
  by split => //; exact: variations_neq0.
  by split => //; exact: variations_neq0.
apply: le_sup.
- move=> r/= [s [l' acl' <-{s}]] [t [l cbl] <-{t} <-{r}].
  exists (variation a b f (l' ++ l)); split; last by rewrite variationD// ltW.
  exact/variations_variation/(itv_partition_cat acl' cbl).
- have [r acfr] := variations_neq0 f ac.
  have [s cbfs] := variations_neq0 f cb.
  by exists (r + s); exists r => //; exists s.
- by split => //; apply: variations_neq0; rewrite (lt_trans ac).
Qed.

Let total_variationD2 a b c f : a <= c -> c <= b ->
  (TV a b f <= TV a c f + TV c b f)%E.
Proof.
rewrite le_eqVlt => /predU1P[<-{c}|ac]; first by rewrite total_variationxx add0e.
rewrite le_eqVlt => /predU1P[<-{b}|cb]; first by rewrite total_variationxx adde0.
case : (pselect (bounded_variation a c f)); first last.
  move=> nbdac; have /eqP -> : TV a c f == +oo%E.
    have: (-oo < TV a c f)%E by apply: (lt_le_trans _ (total_variation_ge0 f (ltW ac))).
    by rewrite ltNye_eq => /orP [] => // /bounded_variationP => /(_ (ltW ac)).
  by rewrite addye ?leey // -ltNye (@lt_le_trans _ _ 0)%E // ?total_variation_ge0 // ltW.
case : (pselect (bounded_variation c b f)); first last.
  move=> nbdac; have /eqP -> : TV c b f == +oo%E.
    have: (-oo < TV c b f)%E.
      exact: (lt_le_trans _ (total_variation_ge0 f (ltW cb))).
    by rewrite ltNye_eq => /orP [] => // /bounded_variationP => /(_ (ltW cb)).
  rewrite addey ?leey // -ltNye (@lt_le_trans _ _ 0%E)//.
  exact/total_variation_ge0/ltW.
move=> bdAB bdAC.
rewrite /total_variation [x in (x + _)%E]ereal_sup_EFin //; last first.
  exact: variations_neq0.
rewrite [x in (_ + x)%E]ereal_sup_EFin //; last exact: variations_neq0.
rewrite -EFinD -sup_sumE /has_sup; [|(by split => //; exact: variations_neq0)..].
apply: ub_ereal_sup => ? [? [l pacl <- <-]]; rewrite lee_fin.
apply: (le_trans (variation_itv_partitionLR _ ac _ _)) => //.
apply: sup_ub => /=.
  case: bdAB => M ubdM; case: bdAC => N ubdN; exists (N + M).
  move=> q [?] [i pabi <-] [? [j pbcj <-]] <-.
  by apply: lerD; [apply: ubdN;exists i|apply:ubdM;exists j].
exists (variation a c f (itv_partitionL l c)).
  by apply: variations_variation; exact: itv_partitionLP pacl.
exists (variation c b f (itv_partitionR l c)).
  by apply: variations_variation; exact: itv_partitionRP pacl.
by rewrite variationD// ?ltW//;
  [exact: itv_partitionLP pacl|exact: itv_partitionRP pacl].
Qed.

Lemma total_variationD a b c f : a <= c -> c <= b ->
  (TV a b f = TV a c f + TV c b f)%E.
Proof.
by move=> ac cb; apply/eqP; rewrite eq_le; apply/andP; split;
  [exact: total_variationD2|exact: total_variationD1].
Qed.

End total_variation.

Section variation_continuity.
Context {R : realType}.
Implicit Type f : R -> R.

Notation BV := bounded_variation.
Notation TV := total_variation.

Definition neg_tv a f (x : R) : \bar R := ((TV a x f - (f x)%:E) * 2^-1%:E)%E.

Definition pos_tv a f (x : R) : \bar R := neg_tv a (\- f) x.

Lemma neg_tv_nondecreasing a b f :
  {in `[a, b] &, nondecreasing_fun (neg_tv a f)}.
Proof.
move=> x y xab yab xy; have ax : a <= x.
  by move: xab; rewrite in_itv //= => /andP [].
rewrite /neg_tv lee_pmul2r // lee_subr_addl // addeCA -EFinB.
rewrite [TV a y _](total_variationD _ ax xy) //.
apply: lee_add => //; apply: le_trans; last exact: total_variation_ge.
by rewrite lee_fin ler_norm.
Qed.

Lemma bounded_variation_pos_neg_tvE a b f : BV a b f ->
  {in `[a, b], f =1 (fine \o pos_tv a f) \- (fine \o neg_tv a f)}.
Proof.
move=> bdabf x; rewrite in_itv /= => /andP [ax xb].
have ffin: TV a x f \is a fin_num.
   apply/bounded_variationP => //.
   exact: (bounded_variationl _ xb).
have Nffin : TV a x (\- f) \is a fin_num.
  apply/bounded_variationP => //; apply/bounded_variationN.
  exact: (bounded_variationl ax xb).
rewrite /pos_tv /neg_tv /= total_variationN -fineB -?muleBl // ?fineM //.
- rewrite addeAC oppeD //= ?fin_num_adde_defl //.
  by rewrite addeA subee // add0e -EFinD //= opprK mulrDl -Num.Theory.splitr.
- by rewrite fin_numB ?fin_numD ?ffin; apply/andP; split.
- by apply: fin_num_adde_defl; rewrite fin_numN fin_numD; apply/andP; split.
- by rewrite fin_numM // fin_numD; apply/andP; split.
- by rewrite fin_numM // fin_numD; apply/andP; split.
Qed.

Lemma fine_neg_tv_nondecreasing a b f : BV a b f ->
  {in `[a, b] &, nondecreasing_fun (fine \o neg_tv a f)}.
Proof.
move=> bdv p q pab qab pq /=.
move: (pab) (qab); rewrite ?in_itv /= => /andP[ap pb] /andP[aq qb].
apply: fine_le; rewrite /neg_tv ?fin_numM // ?fin_numB /=.
- apply/andP; split => //; apply/bounded_variationP => //.
  exact: (bounded_variationl _ pb).
- apply/andP; split => //; apply/bounded_variationP => //.
  exact: (bounded_variationl _ qb).
exact: (neg_tv_nondecreasing _ pab).
Qed.

Lemma neg_tv_bounded_variation a b f : BV a b f -> BV a b (fine \o neg_tv a f).
Proof.
move=> ?; apply: nondecreasing_bounded_variation.
exact: fine_neg_tv_nondecreasing.
Qed.

Lemma total_variation_right_continuous a b x f : a <= x -> x < b ->
  f @ x^'+ --> f x ->
  BV a b f ->
  fine \o TV a ^~ f @ x^'+ --> fine (TV a x f).
Proof.
move=> ax xb ctsf bvf; have ? : a <= b by apply:ltW; apply: (le_lt_trans ax).
apply/cvgrPdist_lt=> _/posnumP[eps].
have ? : Filter (nbhs x^'+) by exact: at_right_proper_filter.
have xbl := ltW xb.
have xbfin : TV x b f \is a fin_num.
  by apply/bounded_variationP => //; exact: (bounded_variationr _ _ bvf).
have [//|?] := @ub_ereal_sup_adherent R _ (eps%:num / 2) _ xbfin.
case=> ? [l + <- <-]; rewrite -/(total_variation x b f).
move: l => [|i j].
  by move=> /itv_partition_nil /eqP; rewrite lt_eqF.
move=> [/= /andP[xi ij /eqP ijb]] tv_eps.
apply: filter_app (nbhs_right_ge _).
apply: filter_app (nbhs_right_lt xi).
have e20 : 0 < eps%:num / 2 by [].
move/cvgrPdist_lt/(_ (eps%:num/2) e20) : ctsf; apply: filter_app.
near=> t => fxt ti xt; have ta : a <= t by exact: (le_trans ax).
have tb : t <= b by rewrite (le_trans (ltW ti))// -ijb path_lt_le_last.
rewrite -fineB; last 2 first.
  by apply/bounded_variationP => //; exact: bounded_variationl bvf.
  by apply/bounded_variationP => //; exact: bounded_variationl bvf.
rewrite (total_variationD _ ax xt).
have tbfin : TV t b f \is a fin_num.
  by apply/bounded_variationP => //; exact: (@bounded_variationr _ a).
have xtfin : TV x t f \is a fin_num.
  apply/bounded_variationP => //; apply: (@bounded_variationl _ _ _ b) => //.
  exact: (@bounded_variationr _ a).
rewrite oppeD ?fin_num_adde_defl// addeA subee //; first last.
  by apply/bounded_variationP => //; exact: (@bounded_variationl _ _ _ b).
rewrite sub0e fineN normrN ger0_norm; last first.
  by rewrite fine_ge0// total_variation_ge0.
move: (tv_eps); rewrite (total_variationD f _ tb) //.
move: xt; rewrite le_eqVlt => /predU1P[->|xt].
  by rewrite total_variationxx/=.
have : variation x b f (i :: j) <= variation x t f (t :: nil) +
                                   variation t b f (i :: j).
  rewrite variationD//; last 2 first.
    exact: itv_partition1.
    by rewrite /itv_partition/= ti ij ijb.
  exact: le_variation.
rewrite -lee_fin => /lt_le_trans /[apply].
rewrite {1}variation_prev; last exact: itv_partition1.
rewrite /= -addeA -lte_subr_addr; last by rewrite fin_numD; apply/andP.
rewrite EFinD -lte_fin ?fineK // oppeD //= ?fin_num_adde_defl // opprK addeA.
move/lt_trans; apply.
rewrite [x in (_ < x%:E)%E]Num.Theory.splitr EFinD addeC lte_add2lE //.
rewrite -addeA.
apply: (@le_lt_trans _ _ (variation x t f (t :: nil))%:E).
  rewrite [in leRHS]variation_prev; last exact: itv_partition1.
  rewrite gee_addl // sube_le0; apply: ereal_sup_ub => /=.
  exists (variation t b f (i :: j)) => //; apply: variations_variation.
  by rewrite /itv_partition/= ijb ij ti.
by rewrite /variation/= big_nat_recr//= big_nil add0r distrC lte_fin.
Unshelve. all: by end_near. Qed.

Lemma neg_tv_right_continuous a x b f : a <= x -> x < b ->
  BV a b f ->
  f @ x^'+ --> f x ->
  fine \o neg_tv a f @ x^'+ --> fine (neg_tv a f x).
Proof.
move=> ax ? bvf fcts; have xb : x <= b by exact: ltW.
have xbfin : TV a x f \is a fin_num.
  by apply/bounded_variationP => //; exact: bounded_variationl bvf.
apply: fine_cvg; rewrite /neg_tv fineM // ?fin_numB ?xbfin //= EFinM.
under eq_fun => i do rewrite EFinN.
apply: (@cvg_trans _ (((TV a n f - (f n)%:E) * 2^-1%:E)%E @[n --> x^'+])).
  exact: cvg_id.
apply: cvgeMr; first by [].
rewrite fineD; [|by []..].
rewrite EFinB; apply: cvgeB; [by []| |].
  apply/ fine_cvgP; split; first exists (b - x).
  - by rewrite /= subr_gt0.
  - move=> t /= xtbx xt; have ? : a <= t.
      by apply: ltW; apply: (le_lt_trans ax).
    apply/bounded_variationP => //.
    apply: bounded_variationl bvf => //.
    move: xtbx; rewrite distrC ger0_norm ?subr_ge0; last by exact: ltW.
    by rewrite ltrBrDr -addrA [-_ + _]addrC subrr addr0 => /ltW.
  by apply: total_variation_right_continuous => //; last exact: bvf.
apply: cvg_comp; first exact: fcts.
apply/ fine_cvgP; split; first by near=> t => //.
by have -> : fine \o EFin = id by move=> ?; rewrite funeqE => ? /=.
Unshelve. all: by end_near. Qed.

Lemma total_variation_opp a b f : TV a b f = TV (- b) (- a) (f \o -%R).
Proof. by rewrite /total_variation variations_opp. Qed.

Lemma total_variation_left_continuous a b x f : a < x -> x <= b ->
  f @ x^'- --> f x ->
  BV a b f ->
  fine \o TV a ^~ f @ x^'- --> fine (TV a x f).
Proof.
move=> ax xb fNcts bvf.
apply/cvg_at_leftNP; rewrite total_variation_opp.
have bvNf : BV (-b) (-a) (f \o -%R).
  by case: bvf => M; rewrite -variations_opp => ?; exists M.
have bx : - b <= - x by rewrite lerNl opprK.
have xa : - x < - a by rewrite ltrNl opprK.
have ? : - x <= - a by exact: ltW.
have ? : Filter (nbhs (-x)^'+) by exact: at_right_proper_filter.
have -> : fine (TV (-x) (-a) (f \o -%R)) =
    fine (TV (-b) (-a) (f \o -%R)) - fine (TV (-b) (-x) (f \o -%R)).
  apply/eqP; rewrite -subr_eq opprK addrC.
  rewrite -fineD; last 2 first.
    by apply/bounded_variationP => //; exact: bounded_variationl bvNf.
    by apply/bounded_variationP => //; exact: bounded_variationr bvNf.
  by rewrite -total_variationD.
have /near_eq_cvg/cvg_trans : {near (- x)^'+,
    (fun t => fine (TV (- b) (- a) (f \o -%R)) - fine (TV (- b) t (f \o -%R))) =1
    (fine \o (TV a)^~ f) \o -%R}.
  apply: filter_app (nbhs_right_lt xa).
  apply: filter_app (nbhs_right_ge _).
  near=> t => xt ta; have ? : -b <= t by exact: (le_trans bx).
  have ? : t <= -a by exact: ltW.
  apply/eqP; rewrite eq_sym -subr_eq opprK addrC.
  rewrite /= [TV a _ f]total_variation_opp opprK -fineD; last first.
    by apply/bounded_variationP => //; apply: bounded_variationr bvNf.
    by apply/bounded_variationP => //; apply: bounded_variationl bvNf.
  by rewrite -total_variationD.
apply.
apply: cvgB; first exact: cvg_cst.
apply: (total_variation_right_continuous _ _ _ bvNf).
- by rewrite lerNl opprK //.
- by rewrite ltrNl opprK //.
by apply/cvg_at_leftNP; rewrite /= opprK.
Unshelve. all: by end_near. Qed.

Lemma total_variation_continuous a b (f : R -> R) : a < b ->
  {within `[a,b], continuous f} ->
  BV a b f ->
  {within `[a,b], continuous (fine \o TV a ^~ f)}.
Proof.
move=> ab /(@continuous_within_itvP _ _ _ _ ab) [int [l r]] bdf.
apply/continuous_within_itvP; (repeat split) => //.
- move=> x /[dup] xab; rewrite in_itv /= => /andP [ax xb].
  apply/left_right_continuousP; split.
    apply: (total_variation_left_continuous _ (ltW xb)) => //.
    by have /left_right_continuousP [] := int x xab.
  apply: (total_variation_right_continuous _ xb) => //; first exact: ltW.
  by have /left_right_continuousP [] := int x xab.
- exact: (total_variation_right_continuous _ ab).
- exact: (total_variation_left_continuous ab).
Qed.

End variation_continuity.
*)


(* TODO: move to topology.v *)
Section Gdelta.
Context (R : topologicalType).

Definition Gdelta (S : set R) :=
  exists A_ : (set R)^nat, (forall i, open (A_ i)) /\ S = \bigcap_i (A_ i).

Lemma open_Gdelta (S : set R) : open S -> Gdelta S.
Proof.
pose S_ (i : nat) := bigcap2 S setT i.
exists S_; split.
- move=> i.
  rewrite /S_ /bigcap2.
  case: ifP => // _.
  by case: ifP => // _; apply: openT.
- by rewrite bigcap2E setIT.
Qed.

End Gdelta.

Section Banach_Zarecki.
Context (R : realType).
Context (m := (@lebesgue_measure R)).
Context (a b : R) (ab : a < b).

Let Borel := @measurable _ R.

Let Lusin (f : R -> R) := (forall E : set R, m E = 0%E -> m (image E f) = 0%E).

Let H f x := total_variation a x f.

Lemma total_variation_Lusin (f : R -> R) :
{within `[a, b], continuous f}
  -> bounded_variation a b f
  -> Lusin (fun x => fine (H f x))
  -> Lusin f.
Proof.
Admitted.

Lemma Lusin_total_variation (f : R -> R) :
{within `[a, b], continuous f}
  -> bounded_variation a b f
  -> Lusin f
  -> Lusin (fun x => fine (H f x)).
Proof.
Admitted.

Let B (f : R -> R) := [set y | exists x, x \in `[a, b] /\ f@^-1` [set y] = [set x]].

Lemma nondecreasing_fun_cmplB_borel f :
{in `[a, b] &, {homo f : x y / x <= y}}
  -> Borel (`[f a, f b]%classic `\` (B f)).
Proof.
Admitted.

Lemma nondecreasing_fun_image_Gdelta_borel f (Z : set R) :
{in `[a, b] &, {homo f : x y / x <= y}}
  -> Z `<=` `]a, b[%classic
  -> Gdelta Z
  -> Borel [set f x | x in Z].
Proof.
Admitted.

Lemma nondecreasing_fun_image_measure (f : R -> R) (G_ : (set R)^nat) :
{in `[a, b] &, {homo f : x y / x <= y}}
  -> \bigcap_i G_ i `<=` `]a, b[%classic
  -> m (\bigcap_i (G_ i)) = \sum_(i \in setT) (m (G_ i)).
Proof.
Admitted.

Lemma Banach_Zarecki_increasing (f : R -> R) :
{within `[a, b], continuous f}
  -> {in `[a, b]  &, {homo f : x y / x <= y}}
  -> bounded_variation a b f
  -> Lusin f
  -> abs_cont a b f.
Proof.
move=> cf incf bvf Lf.
case: (EM (abs_cont a b f)) => //.
move/existsNP => [e0].
move/forallNP => nacf.
apply: False_ind.

have p2' (n : nat) : (0 < (1 / 2 ^ n)).
  admit.
pose p2 := p2' R.
pose d_ (n : nat) : {posnum R} := PosNum (p2 n).

have := (fun n => nacf (d_ n)).
move/(_ _)/existsNP.
move/choice.
move/(_ _ _)/existsNP.
Admitted.

Let H' (f : R -> R) (x : R) := fine (H f x).

(* Lemma total_variation_BV (f : R -> R) : *)
(* bounded_variation a b (H' f) -> bounded_variation a b f. *)
(* Proof. *)
(* move=> bvH'. *)
(* have able : a <= b. *)
(*   by apply/ltW. *)
(* apply/bounded_variationP => //. *)
(* rewrite ge0_fin_numE; last by apply: total_variation_ge0. *)
(* apply: (@le_lt_trans _ _ (total_variation a b (H' f))); last first. *)
(*   rewrite -ge0_fin_numE; last by apply: total_variation_ge0. *)
(*   by apply/bounded_variationP. *)
(* apply: ub_ereal_sup => xe /= [] x /[swap] <- {xe}. *)
(* rewrite /variations => /=. *)
(* move/cid2 => [] s itvs <-. *)
(* apply: ereal_sup_le. *)
(* exists (variation a b (H' f) s)%:E. *)
(*   move=> //. *)
(*   exists (variation a b (H' f) s) => //. *)
(*   exact: variations_variation. *)
(* rewrite !variation_next //. *)
(* elim: s itvs; first by move=> ?; rewrite !big_nil. *)
(* move=> h t IH ht. *)
(* rewrite /= !big_cons. *)
(* rewrite !EFinD. *)
(* rewrite lee_add => //. *)
(* - have ah : a <= h. *)
(*     admit. *)
(*   have hb : h <= b. *)
(*     admit. *)
(*   unlock => /=. *)
(*   rewrite !ifT => //. *)
(*   rewrite /H' /H total_variationxx fine0 subr0. *)
(*   rewrite [X in (_ <= X%:E)%E]ger0_norm; last by rewrite fine_ge0 // total_variation_ge0. *)
(*   (* BV f ? *) admit. *)
(* rewrite !big_seq. *)
(* apply: ler_sum => e eht. *)
(* pose ne := next (locked (h :: t)) e; fold ne. *)
(* have ae : a <= e. *)
(*   admit. *)
(* have ene : e <= ne. *)
(*   admit. *)
(* have neb : ne <= b. *)
(*   admit. *)
(* rewrite /H' /H (total_variationD _ ae) //; last first. *)
(*   admit. *)
(* rewrite fineD; last 2 first. *)
(*     (* BV f ? *) admit. *)
(*   admit. *)
(* rewrite addrAC subrr add0r. *)
(* Abort. *)

Lemma total_variation_AC (f : R -> R) :
bounded_variation a b f ->
abs_cont a b (H' f) -> abs_cont a b f.
Proof.
move=> bvH' acH' e.
have := acH' e.
move: (acH') => _ [d ac'H'].
exists d => I B trivB.
have := ac'H' I B trivB.
move: trivB => [/all_and2 [B21 Bab] [trivB sumBd sumHd]].
apply: (le_lt_trans _ sumHd).
apply: ler_sum => i iI.
have aB1 : a <= (B i).1.
  move: (Bab i).
  move/in1_subset_itv.
  move/(_ (fun x => a <= x)).
  apply.
    by move=> x; rewrite in_itv /= => /andP [].
  by rewrite in_itv /= B21 andbT.
have B2b : (B i).2 <= b.
  move: (Bab i).
  move/in1_subset_itv.
  move/(_ (fun x => x <= b)).
  apply.
    by move=> x; rewrite in_itv /= => /andP [].
  by rewrite in_itv /= B21 andTb.
have able : a <= b.
  by apply/ltW.
apply: (le_trans (ler_norm (f (B i).2 - f (B i).1))).
rewrite /H' /H.
rewrite (@total_variationD _ a (B i).2 (B i).1 f) => //.
rewrite fineD; last 2 first.
- apply/bounded_variationP => //.
  by apply: (@bounded_variationl _ _ _ b) => //; first apply: (le_trans _ B2b).
- apply/bounded_variationP => //.
  apply: (bounded_variationl _ B2b) => //.
  by apply: (bounded_variationr aB1) => //; first apply: (le_trans _ B2b).
rewrite addrAC subrr add0r.
rewrite -[leLHS]add0r -ler_subr_addr.
rewrite -lee_fin.
rewrite EFinB.
rewrite fineK; last first.
  apply/bounded_variationP => //.
  apply: (bounded_variationl _ B2b) => //.
  by apply: (bounded_variationr aB1); first apply: (@le_trans _ _ (B i).2).
rewrite lee_subr_addr; last first.
  rewrite ge0_fin_numE; last exact: normr_ge0.
  exact: ltry.
rewrite add0e.
by apply: total_variation_ge.
Qed.

Lemma TV_nondecreasing (f : R -> R) :
bounded_variation a b f -> {in `[a, b] &, {homo H' f : x y / x <= y}}.
Proof.
move=> bvf x y xab yab xy.
have ax : a <= x.
  move: xab.
  rewrite in_itv /=.
  by move/andP => [].
have yb : y <= b.
  move: yab.
  rewrite in_itv /=.
  by move/andP => [].
rewrite fine_le => //.
    apply/bounded_variationP => //.
    apply: (@bounded_variationl _ a x b) => //.
    by apply: (le_trans xy).
  apply/bounded_variationP.
    by apply: (le_trans ax).
  apply: (bounded_variationl _ yb) => //.
  by apply: (le_trans ax).
rewrite /H (@total_variationD _ a y x) //; last first.
apply: lee_addl.
exact: total_variation_ge0.
Qed.

Lemma TV_bounded_variation (f : R -> R) :
bounded_variation a b f -> bounded_variation a b (H' f).
Proof.
move=> bvf.
apply/bounded_variationP; rewrite ?ltW //.
rewrite ge0_fin_numE; last by apply: total_variation_ge0; rewrite ltW.
rewrite nondecreasing_total_variation; rewrite ?ltW //; first exact: ltry.
exact: TV_nondecreasing.
Qed.

Theorem Banach_Zarecki (f : R -> R) :
{within `[a, b], continuous f} -> bounded_variation a b f
  -> Lusin f
  -> abs_cont a b f.
Proof.
move=> cf bvf Lf.
apply: total_variation_AC => //.
apply: Banach_Zarecki_increasing.
      exact: total_variation_continuous.
    exact: TV_nondecreasing.
  exact: TV_bounded_variation.
exact: Lusin_total_variation.
Qed.

End Banach_Zarecki.
