From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
From mathcomp.classical Require Import set_interval.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import derive realfun exp trigo lebesgue_measure lebesgue_integral.
Require Import numfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section AC.

Variable (R : realType).

Local Definition cball (xr : R * {posnum R}) := @closed_ball_ R R normr xr.1 xr.2%:num.
(*(B : R * {posnum R}) := [set y | `|B.1 - y| <= B.2%:num].*)

Definition AC (a : R) (r : {posnum R}) (f : R -> R) := forall e : {posnum R},
  exists d : {posnum R}, forall (I : finType) (B : I -> R * {posnum R}),
    (forall i, cball (B i) `<=` `[a, a + r%:num]) /\
    trivIset setT (cball \o B) /\
    \sum_(k in I) (B k).2%:num < d%:num ->
    \sum_(k in I) (f ((B k).1 + (B k).2%:num) - f ((B k).1 - (B k).2%:num)) < e%:num.

Lemma lipschitz_is_AC (a : R) (r : {posnum R}) (f : R^o -> R^o) :
  [lipschitz f x | x in `[a, a + r%:num]] -> AC a r f.
Proof.
move=> [L [_ lipf]] e.
pose d := (2 * (`|L| + 1))^-1 * e%:num. (* TODO : e%:num / (`|L| + 1) *)
have dgt0 : 0 < d by apply: mulr_gt0.
exists (PosNum dgt0) => /=.
move=> I B [Bar [trivB sum_ltd]].
apply: (@le_lt_trans _ _ (\sum_(k in I)
    `|f ((B k).1 + (B k).2%:num) - f ((B k).1 - (B k).2%:num)|)).
  by rewrite ler_sum // => k _ /=; rewrite ler_norm.
have LL1 : L < (`|L| + 1) by rewrite (le_lt_trans (ler_norm _)) // ltr_addl.
apply: (@le_lt_trans _ _ (\sum_(k in I) 2 * (`|L| + 1) * (B k).2%:num)).
  rewrite ler_sum => //= k _.
  have := lipf _ LL1 ((B k).1 + (B k).2%:num, (B k).1 - (B k).2%:num) => /=.
  rewrite {3}addrC addrKA opprK -mulr2n normrMn -(mulr_natl `|(B k).2%:num| 2).
  rewrite mulrCA mulrA (@gtr0_norm _ (B k).2%:num) // => -> //.
  split; apply: (Bar k) => /=; rewrite /cball /closed_ball_ /= -{1}(add0r (B k).1) addrKA sub0r.
    by rewrite ltr0_norm // opprK.
  by rewrite opprK gtr0_norm.
by rewrite -mulr_sumr -ltr_pdivlMl.
Qed.

End AC.

(* Definition is_part_citv (a b : R) (s : seq R) := path ltr a (s ++ [:: b]). *)
Record isPartition (R : realType) (a b : R) (l : list R) :=
{ head_a : forall x, head x l = a;
  last_b : forall x, last x l = b;
  ler_path : pairwise ler l
}.

(* can't define HB.structures? *)
Unset Printing Notations.
Definition Partition (R : realType) (a b : R) := {l | isPartition a b l}.
(* Defining as { l of isPartition a b l} is sigT with unneccesary True, why? *)

Section partition_properties.

Variable R : realType.
Variables (a b c : R).

Definition Partition_lbound (l : Partition a b) := b.
Definition Partition_ubound (l : Partition a b) := a.

Definition concat_Partition (lab : Partition a b) (lbc : Partition b c) 
: Partition a c.
Proof.
move: lab lbc.
move=> [l [lha llb pltrl]].
move=> [s [shb slb pltrs]].
have t := l ++ s.
exists t.
split => //.
    admit.
  admit.
admit.
Admitted.

Definition cut_Partition (lab : Partition a b) (x : R) :
  (Partition a x) * (Partition x b).
Proof.
move: lab => [] l [] h_la l_lb pler_l.
pose lx := [seq y <- l | y <= x] ++ [:: x] : seq R.
pose xl := x :: [seq z <- l | x <= z] : seq R.
have h_lxa : forall t : R, head t lx = a.
  admit.
have l_lxl : forall t : R, last t lx = x.
  admit.
have pler_lx : pairwise ler lx.
  admit.
have h_xlx : forall t : R, head t xl = x.
  admit.
have l_xlb : forall t : R, last t xl = b.
  admit.
have pler_xl : pairwise ler xl.
  admit.
split.
  by exists lx; split.
by exists xl; split.
Admitted.

Definition cutr_Partition (lab : Partition a b) (x : R) : Partition a x :=
  let (l, _) := cut_Partition lab x in l.

Definition cutl_Partition (lab : Partition a b) (x : R) : Partition x b :=
  let (_, r) := cut_Partition lab x in r.

Definition list_of_Partition (l : Partition a b)
  : list R := proj1_sig l.


End partition_properties.


Notation "x :: s" := (concat_Partition x s).


Section variation.

Variable R : realType.
Variables (a b c : R).

Definition variation (f : R -> R) (s : Partition a b) :=
\sum_(i <- (Partition_is_list s)) `| f (next (Partition_is_list s) i) - f i|.

Lemma variation_ge0 f (s : Partition a b) :
 0 <= variation f s. Proof. exact: sumr_ge0. Qed.

Lemma variation_ge f s : `|f b - f a| <= variation f s.
Proof. rewrite /variation big_seq1 /= ifT. Qed.

Lemma variation_cons a b f h rs :
  variation a b f (h :: rs) = `|f h - f a| + variation h b f rs.
Proof.
rewrite /variation.
rewrite big_cons /=.
rewrite ifT //.
congr (_ + _).
rewrite !big_seq.
apply: eq_bigr => i.
(* unprovable? *)
Abort.

Lemma path_trans (T : eqType) (e : rel T) (trans_e : transitive e)
(x x' : T) (s : seq T) :  e x x' -> path e x' s ->
forall i : T, i \in s -> e x i.
Proof.
move=> xx' x's.
apply/allP.



elim: s x's => // b l IH /= /andP [xb bl] i.
rewrite in_cons => /orP [/eqP ->|] //.
  by apply (trans_e _ _ _ xx').
by apply IH, (path_le trans_e xb).
Qed.

(* a s0 s1 ... sn c t0 t1 ... tm b -> a s0 ... sn c + c t0 ... tm b *)
Lemma variation_cat a b f s (c : R) :c \in s ->
  variation a b f s =
   variation a c f (take (index c s) s)
     + variation c b f (drop (index c s).+1 s).
Proof.
Abort.

(* memo sumEFin : (\sum)%E=(\sum)%:E *)
Definition total_variation (a b : R) (f : R -> R) : \bar R :=
ereal_sup [set (variation a b f s)%:E | s in [set s | path ltr a (s ++ [:: b])]].

Lemma total_variation_nil a b f:
  b <= a -> total_variation a b f = -oo%E.
Proof.
move=> ba.
rewrite /total_variation.
apply /eqP.
rewrite -leeNy_eq.
rewrite -ereal_sup0.
apply le_ereal_sup.
rewrite subset0.
rewrite -(image_set0 (fun x=> (variation a b f x)%:E)).
congr ([set _ | _ in _]).
apply: eq_set => x.
rewrite lt_path_sortedE.
rewrite -falseE.
rewrite (_:all (> a) (x ++ [:: b]) = false) //.
apply /negP.
rewrite all_cat all_seq1.
move /andP => [_].
rewrite ltNge.
apply /negP.
by rewrite negbK.
Qed.

Lemma total_variation_ge0 (a b : R) (f: R -> R) : a < b -> (0 <= total_variation a b f)%E.
Proof.
move=> ab.
apply: (@le_trans _ _ (`|f b - f a|%:E)) => //.
apply: ge_supremum_Nmem => /=.
  exact: ereal_supremums_neq0.
exists [::].
  by rewrite lt_path_sortedE /= !andbT.
rewrite /variation.
rewrite big_seq1 /=.
rewrite ifT //.
Qed.

Definition BV a b f := total_variation a b f \is a fin_num.

Lemma BV_in (a b : R) (f : R -> R) (bvf : BV a b f)
  (x y : R) (ax : a <= x) : x < y <= b -> BV x y f.
Proof.
move/andP => [xy yb].
rewrite /BV ge0_fin_numE; last first.
  by apply: total_variation_ge0.
apply: (@le_lt_trans _ _ (total_variation a b f)); last first.
  rewrite -ge0_fin_numE; last first.
    apply: total_variation_ge0.
    apply: (@le_lt_trans _ _ x a b) => //.
    by apply: (lt_le_trans xy).
  exact: bvf.
apply ub_ereal_sup.
rewrite /ubound /=.
move=> v /= [s ps] <-.
move: ax; rewrite le_eqVlt; move/orP => [/eqP -> | ax].
  rewrite (@le_trans _ _ (variation x b f (s ++ [:: y]))%:E) //.
    rewrite lee_tofin //.
    rewrite /variation (big_cat _ (x :: s) [:: y]) //.
    rewrite big_seq1 -[leLHS]addr0 lerD => [//||]; last first.
      rewrite (_:next (x :: (s ++ [:: y]) ++ [:: b]) y = b) => //.
      rewrite next_nth.
      rewrite ifT; last first.
      rewrite inE; apply/orP; right.
      rewrite mem_cat; apply/orP; left.
      rewrite mem_cat; apply/orP; right.
      by rewrite mem_seq1.
      admit.
    rewrite /=.
    (* lemma? *)
    admit.
  admit.
Admitted.

Lemma BV_inr a b f (bvf : BV a b f) (x : R) : a < x -> x <= b -> BV a x f.
Proof.
move=> ax xb.
apply: (@BV_in _ _ _ bvf a x) => //.
by rewrite ax xb.
Admitted.

Lemma AC_is_BV (a : R) (d : {posnum R}) (f : R -> R) :
  AC a d f -> BV a (a + d%:num) f.
Proof.
Admitted.

Definition total_variation_fun (a b : R) (f : R -> R) (x : R) : R :=
if x < a then 0
  else if x <= b then fine (total_variation a x f)
       else fine (total_variation a b f).

Section total_variation_properties.

Variables (a b c: R) (f g: R -> R).
Let T := total_variation_fun a b f.

Lemma total_variationD :
total_variation a c f = (total_variation b c f + total_variation a b f)%E.
Proof.
Admitted.

Lemma total_variation_fun_ge0 : {in `[a, b], forall x, 0 <= T x}.
Proof.
move=> x.
rewrite in_itv /=.
move/andP => [].
  rewrite le_eqVlt.
  move/orP => [/eqP <- _|ax xb];rewrite /T /total_variation_fun.
  rewrite ifF //.
  case: ifP.
    move=> _.
    by rewrite total_variation_nil.
  move/negbT.
  rewrite -ltNge.
  move/ltW => ba.
  by rewrite total_variation_nil.
case: ifP => // _.
case: ifP => // _.
  apply: fine_ge0.
  by apply: total_variation_ge0.
have ab: a < b.
  by apply: (lt_le_trans ax).
apply: fine_ge0.
by apply: total_variation_ge0.
Qed.

Lemma BVP :
BV a b f <-> (forall x, total_variation a x f < +oo)%E.
Proof.
Admitted.

Lemma total_variation_is_nondecreasing : BV a b f ->
 {in `[a, b], {homo
  (total_variation_fun a b f) : x y / x <= y}}.
Proof.
Admitted.

Lemma total_variation_fun_diff_dominates :
  forall x y,
    f x - f y <= total_variation_fun a b f x - total_variation_fun a b f y.
Proof.
Admitted.

End total_variation_properties.

(* TODO *)
Variable right_continuous : forall R : Type, (R -> R) -> Prop.

HB.mixin Record isCumulative (R : realType) (a b : R) (f : R -> R) := {
homof : {in `[a, b], {homo f : x y / x <= y}};
rcf : right_continuous f
}.

#[short(type=Cumulative)]
HB.structure Definition Cumulative R a b := {f of isCumulative R a b f}.

Section BV_decomp.

Variables (a b : R).
Variable (f : R -> R).
Hypothesis (bvf : BV a b f).

Let T := (total_variation_fun a b f).

Let Tf_nondec : {in `[a, b], {homo (T - f) : x y / x <= y}}.
Proof.
Admitted.

Lemma BV_decomp :
  exists g h : R -> R,
    [/\ {in `[a, b], {homo g : x y / x <= y}},
    {in `[a, b], {homo h : x y / x <= y}} &
    {in `[a, b], f =1 g \- h}].
Proof.
exists T.
exists (T \- f).
split.
    rewrite /T.
    move=> x xab y xy.
    apply: total_variation_is_nondecreasing => //.
  exact: Tf_nondec.
move=> x _ /=.
by rewrite opprB addrCA subrr addr0.
Admitted.

End BV_decomp.
