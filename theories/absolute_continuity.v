From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences real_interval.
Require Import esum measure lebesgue_measure numfun lebesgue_integral.
Require Import realfun exp lebesgue_stieltjes_measure derive.

(**md**************************************************************************)
(* # Absolute Continuity                                                      *)
(* ```                                                                        *)
(*   Gdelta ==                                                                *)
(*   abs_cont ==                                                              *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.


(* TODO: move to topology.v *)
Section Gdelta.
Context (R : realType).

Definition Gdelta (S : set R) :=
  exists2 A_ : (set R)^nat, (forall i, open (A_ i)) & S = \bigcap_i (A_ i).

Lemma open_Gdelta (S : set R) : open S -> Gdelta S.
Proof.
pose S_ i := bigcap2 S setT i.
exists S_.
- move=> i.
  rewrite /S_ /bigcap2.
  case: ifP => // _.
  by case: ifP => // _; apply: openT.
- by rewrite bigcap2E setIT.
Qed.

Lemma Gdelta_measuable (S : set R) : Gdelta S -> (@measurable _ R) S.
Proof.
move=> [] B oB ->.
apply: bigcapT_measurable => i.
by apply: open_measurable.
Qed.

End Gdelta.

(*
Section total_variation_lim.
Context {R : realType}.
Context (a b : R) (f : R -> R).
Context (ab : a < b).

(* subdevide itv_partition by mean *)
Let regular_itv_partition (n : nat) : seq R :=
 [seq (fun (j : nat) => (a + ((b - a) * j))) i | i <- iota 1 n].

Lemma total_variation_lim :
End.
*)

Section absolute_continuity.
Context {R : realType}.

Definition abs_cont (a b : R) (f : R -> R) := forall e : {posnum R},
  exists d : {posnum R}, forall n (B : 'I_n -> R * R),
    [/\ (forall i, (B i).1 <= (B i).2 /\ `[(B i).1, (B i).2] `<=` `[a, b]),
        trivIset setT (fun i => `[(B i).1, (B i).2]%classic) &
        \sum_(k < n) ((B k).2 - (B k).1) < d%:num] ->
    \sum_(k < n) (f (B k).2 - f ((B k).1)) < e%:num.

Lemma total_variation_AC a b (f : R -> R) : a < b ->
  bounded_variation a b f ->
  abs_cont a b (fine \o (total_variation a ^~ f)) -> abs_cont a b f.
Proof.
move=> ab bvH' acH' e.
have := acH' e.
move: (acH') => _ [d ac'H'].
exists d => n B trivB.
have := ac'H' n B trivB.
move: trivB => [/all_and2[B21 Bab]] trivB sumBd sumHd.
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
rewrite /=.
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

Lemma TV_nondecreasing a b (f : R -> R) :
  bounded_variation a b f ->
  {in `[a, b] &, {homo fine \o (total_variation a ^~ f) : x y / x <= y}}.
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
rewrite  (@total_variationD _ a y x) //; last first.
apply: lee_addl.
exact: total_variation_ge0.
Qed.

Lemma TV_bounded_variation a b (f : R -> R) : a < b ->
  bounded_variation a b f -> bounded_variation a b (fine \o (total_variation a ^~ f)).
Proof.
move=> ab bvf.
apply/bounded_variationP; rewrite ?ltW //.
rewrite ge0_fin_numE; last by apply: total_variation_ge0; rewrite ltW.
rewrite nondecreasing_total_variation; rewrite ?ltW //; first exact: ltry.
exact: TV_nondecreasing.
Qed.

End absolute_continuity.

Section wip.
Context {R : realType}.

(* this would be used in abs_cont_bounded_variation *)
Lemma itv_partition_undup_merge (a b : R) (s t : seq R) :
  itv_partition a b s -> itv_partition a b t ->
  itv_partition a b (undup (merge <%R s t)).
Proof.
Abort.

Lemma abs_cont_bounded_variation (a b : R) (f : R -> R) :
  abs_cont a b f -> bounded_variation a b f.
Proof.
Abort.

End wip.

Section lusinN.
Context {R : realType}.
Let mu := @lebesgue_measure R.

Definition lusinN (A : set R) (f : R -> R) :=
  forall E, E `<=` A -> measurable E -> mu E = 0 -> mu (f @` E) = 0.

Definition abs_contN (a b : R) (f : R -> R) :=
  [/\ {within `[a, b]%classic, continuous f},
      bounded_variation a b f &
      lusinN `[a ,b]%classic f].

Fail Lemma lusinN_total_variation a b f : abs_contN a b f ->
  lusinN `[a, b]%classic (total_variation a ^~ f).

Lemma abs_contN_dominates a b (f : cumulative R) : abs_contN a b f ->
  mu `<< lebesgue_stieltjes_measure f.
Abort.

Fail Lemma differentiable_lusinN a b f : {in `]a, b[%classic, differentiable f} ->
  lusinN `]a, b[%classic f.

End lusinN.

(* cannot make instance for now and maybe useless *)
(* Section total_variation_is_cumulative. *)
(* Variable (R : realType) (a b : R) (f : R -> R). *)
(* Variable (ab : a < b). *)
(* Variable (bvf : bounded_variation a b f). *)
(* Let TV := (fine \o total_variation a ^~ f). *)

(* Let TV_nd : {in `[a, b]&, {homo TV : x y / x <= y}}. *)
(* Proof. *)
(* by apply: TV_nondecreasing. *)
(* Qed. *)

(* Let TV_rc : {in `[a, b], right_continuous f}. *)
(* Proof. *)
(* move=>  *)
(* apply: total_variation_right_continuous. *)

(* HB.instance Definition _ := isCumulative.Build R TV TV_nd TV_rc. *)

(* End total_variation_is_cumulative. *)

Section Banach_Zarecki.
Context (R : realType).
Context (m := (@lebesgue_measure R)).
Context (a b : R) (ab : a < b).

Lemma total_variation_Lusin (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] (fun x => fine ((total_variation a ^~ f) x)) ->
  lusinN `[a, b] f.
Proof.
Admitted.

Let increasing_points (f : R -> R) :=
  [set y | exists x, x \in `[a, b] /\ f@^-1` [set y] = [set x]].

Lemma nondecreasing_fun_setD_measurable f :
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  measurable (`[f a, f b]%classic `\` increasing_points f).
Proof.
Abort.

Lemma nondecreasing_fun_image_Gdelta_measurable (f : R -> R) (Z : set R) :
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  Z `<=` `]a, b[%classic ->
  Gdelta Z ->
  measurable (f @` Z).
Proof.
Abort.

Lemma nondecreasing_fun_image_measure (f : R -> R) (G_ : (set R)^nat) :
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  \bigcap_i G_ i `<=` `]a, b[%classic ->
  m (\bigcap_i (G_ i)) = \sum_(i \in setT) (m (G_ i)).
Proof.
Abort.

Lemma Lusin_image_measure0 (f : R -> R) :
{within `[a, b], continuous f} ->
  {in `[a, b]&, {homo f : x y / x <= y}} ->
  lusinN `[a, b] f ->
  exists Z : set R, [/\ Z `<=` `[a, b]%classic,
      compact Z,
      m Z = 0 &
      m (f @` Z) = 0].
Proof.
Admitted.

Lemma image_measure0_Lusin (f : R -> R) :
{within `[a, b], continuous f} ->
  {in `[a, b]&, {homo f : x y / x <= y}} ->
  (forall Z : set R, [/\ measurable Z, Z `<=` `[a, b]%classic,
      compact Z,
      m Z = 0 &
      m (f @` Z) = 0]) ->
  lusinN `[a, b] f.
Proof.
move=> cf ndf clusin.
move=> X Xab mX X0.
Admitted.

Let ex_perfect_set (cmf : cumulative R) (cZ : set R) :
  let f := cmf in
  cZ `<=` `[a, b] ->
  {within `[a, b], continuous f} ->
  {in `[a, b], {homo f : x y / x <= y}} ->
  bounded_variation a b f ->
  exists n, exists I : nat -> R * R,
  (forall i, trivIset setT (fun i => `[(I i).1, (I i).2]%classic) /\
    `](I i).1, (I i).2[ `<=` cZ) /\
     (\sum_(0 <= i < n) `|f (I i).2 - f (I i).1|)%:E
     = lebesgue_stieltjes_measure f cZ.
Proof.
Abort.

(* Lemma 6 *)
Lemma Lusin_total_variation (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] f ->
  lusinN `[a, b] (fun x => fine (total_variation a ^~ f x)).
Proof.
move=> cf bvf lf.
have ndt := (TV_nondecreasing bvf).
have ct :=  (total_variation_continuous ab cf bvf).
apply: image_measure0_Lusin => //.
apply: contrapT.
move=> H.
pose TV := (fine \o (total_variation a)^~ f).
have : exists Z, [/\ Z `<=` `[a, b], compact Z, m Z = 0 & (0 < m (TV @` Z))%E].
  admit.
move=> [Z [abZ cpt_timZ Z0 ptimZ]].
pose c : R := inf Z.
pose d : R := sup Z.
pose alpha := m [set (fine \o (total_variation a)^~ f) x | x in Z].
have rct : right_continuous TV.
  admit.
have monot : {in `[a, b]&, {homo TV : x y / x <= y}}.
  admit.
(*
have : exists n, exists I : (R * R)^nat,
 [/\ (forall i, (I i).1 < (I i).2 /\ `[(I i).1, (I i).2] `<=` `[a, b] ),
     trivIset setT (fun i => `[(I i).1, (I i).2]%classic) &
     \bigcup_(0 <= i < n) (`[(I i).1, (I i).2]%classic) = Z].*)

Admitted.

Lemma Banach_Zarecki_increasing (f : R -> R) :
  {within `[a, b], continuous f} ->
  {in `[a, b]  &, {homo f : x y / x <= y}} ->
  bounded_variation a b f ->
  lusinN `[a, b] f ->
  abs_cont a b f.
Proof.
move=> cf incf bvf lf; apply: contrapT => /existsNP[e0] /forallNP fe0.
have {fe0} : forall d : {posnum R},
    exists n, exists B : 'I_n -> R * R,
      [/\ (forall i, (B i).1 <= (B i).2 /\ `[(B i).1, (B i).2] `<=` `[a, b]),
          trivIset setT (fun i => `[(B i).1, (B i).2]%classic),
          \sum_(k < n) ((B k).2 - (B k).1) < d%:num &
          \sum_(k < n) (f (B k).2 - f (B k).1) >= e0%:num].
  move=> d; have {fe0} := fe0 d.
  move=> /existsNP[n] /existsNP[B] /not_implyP[] [H1 H2 H3 H4].
  by exists n, B; split => //; rewrite leNgt; apply/negP.
move=> /choice[n_0 ab_0].
pose delta_0 (i : nat) : R := (2 ^+ i.+1)^-1.
have delta_0_ge0 (i : nat) : 0 < (2 ^+ i.+1)^-1 :> R by rewrite invr_gt0 exprn_gt0.
pose delta_ (i : nat) : {posnum R} := PosNum (delta_0_ge0 i).
pose n_ i := n_0 (delta_ i).
pose ab_ i : 'I_(n_ i) -> R * R := projT1 (cid (ab_0 (delta_ i))).
have d_prop i : \sum_(k < n_ i) (((ab_ i) k).2 - ((ab_ i) k).1) < delta_0 i.
  by rewrite /ab_; case: cid => ? [].
have e0_prop i : \sum_(k < n_ i) (f (((ab_ i) k).2) - f ((ab_ i) k).1) >= e0%:num.
  by rewrite /ab_; case: cid => ? [].
pose E_ i := \big[setU/set0]_(k < n_ i) `]((ab_ i) k).2, ((ab_ i) k).1[%classic.
pose G_ i := \bigcup_(j in [set j | (j >= i)%N]) E_ j.
pose A := \bigcap_i (G_ i).
have Eled : forall n, (m (E_ n) <= (delta_0 n)%:E)%E.
  move=> t.
  have : m (E_ t) = (\sum_(k < n_ t) ((ab_ t k).2 - (ab_ t k).1))%:E.
    admit.
  move->.
  rewrite lee_fin.
  apply/ltW.
  by apply: d_prop.
have mA0 : lebesgue_measure A = 0.
  rewrite /A.
  have H1 : (m \o G_) x @[x --> \oo] --> m (\bigcap_n G_ n).
    apply: nonincreasing_cvg_mu.
    - move=> /=.
      rewrite (@le_lt_trans _ _ (\sum_(0 <= i <oo) m (E_ i))%E) //.
        apply: measure_sigma_sub_additive.
            move=> n.
            by apply: bigsetU_measurable.
          apply: bigcup_measurable => k _.
          by apply: bigsetU_measurable.
        rewrite /G_.
        apply: bigcup_sub => i _.
        by apply: bigcup_sup.
      apply: (@le_lt_trans _ _ 1%E); last exact: ltry.
      rewrite (_:1%E = (\big[+%R/0%R]_(0 <= i <oo) (delta_0 i)%:E)).
        by apply: lee_nneseries.
      apply: esym.
      rewrite -(_:2^-1 / (1 - 2^-1) = 1); last first.
        have H : 1 - (@GRing.inv R 2) != 0.
          rewrite lt0r_neq0  //.
          rewrite subr_gt0.
          rewrite invf_lt1 //.
          by rewrite ltr1n.
        apply: (@mulIf _ (1 - 2^-1)) => //.
        rewrite mul1r divrK; last by rewrite unitfE.
        rewrite -[X in _ = X - _](@mulfK _ 2) //.
        rewrite mulrC mul1r.
        rewrite mulr_natr [X in X - _]mulrSr mulr1n.
        by rewrite addrK.
      apply: cvg_lim => //.
      apply: cvg_EFin.
        apply: nearW => n.
        by apply/sum_fin_numP.
      under eq_cvg => n.
        rewrite /=.
        rewrite sumEFin /=.
        under eq_bigr => i _.
        rewrite (_:delta_0 i = geometric 2^-1 2^-1 i); last first.
          rewrite /delta_0 /geometric /=.
          by rewrite -exprVn exprS.
          over.
        over.
      apply: cvg_geometric_series.
      rewrite gtr0_norm => //.
      rewrite invf_lt1 //.
      by rewrite ltr1n.
    - admit.
    - admit.
    - admit.
  have : (lebesgue_measure \o G_) x @[x --> \oo] --> 0%E.
    rewrite /=.
    have :  (\forall k \near \oo, (cst 0 k <= (m \o G_) k  <= (delta_0 k.-1)%:E)%E).
      near=> k => /=.
      rewrite measure_ge0 /=.
      apply: (@le_trans _ _ (\big[+%E/0%E]_(k <= j <oo) (m (E_ j))%E)).
        rewrite (_: G_ k = \bigcup_n G_ (n + k)%N); last admit.
        rewrite (_: (\sum_(k <= j <oo) m (E_ j))%E = (\sum_(0 <= j <oo) m (E_ (j + k)%N))%E); last admit.
        apply: measure_sigma_sub_additive.
            admit.
          admit.
        move=> x.
        move=> [/= i _] [j /= ikj Ejx].
        exists (j - k)%N => //.
        rewrite subnK //.
        apply: leq_trans ikj.
        by apply: leq_addl.
      rewrite (_:(delta_0 k.-1)%:E = (\big[+%E/0%E]_(k <= j <oo) (delta_0 j)%:E)); last admit.
      apply: lee_nneseries => // t _.
      have : m (E_ t) = (\sum_(k < n_ t) ((ab_ t k).2 - (ab_ t k).1))%:E.
        admit.
      move->.
      rewrite lee_fin.
      apply/ltW.
      by apply: d_prop.
    move/squeeze_cvge.
    apply.
        exact: cvg_cst.
      have : forall k, (0 < k)%N -> (delta_0 k.-1 = geometric 1 (2 ^-1) k).
        rewrite /geometric /=.
        rewrite /delta_0.
        move=> k k0.
        rewrite prednK //.
        by rewrite -exprVn mul1r.
      move=> Hd.
      apply: cvg_trans.
      apply: near_eq_cvg.
      near=> k.
      rewrite Hd.
      reflexivity.
      near: k.
      by exists 1%N.
    apply: cvg_EFin.
      by near=> k.
    apply: cvg_geometric.
    rewrite gtr0_norm; last first.
      by rewrite invr_gt0.
    rewrite invf_lt1 //.
    by rewrite ltr1n.
  move/cvg_unique : H1.
  move=> /[apply].
  by apply.

have mfA0 : lebesgue_measure (f @` A) = 0.
  (* use lf *)
  apply: lf.
  + rewrite -[X in _ `<=` X](@bigcap_const _ _ (@setT nat) `[a, b]).
    * apply: subset_bigcap => //.
      
  admit.
Admitted.

Theorem Banach_Zarecki (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] f ->
  abs_cont a b f.
Proof.
move=> cf bvf Lf.
apply: total_variation_AC => //.
apply: Banach_Zarecki_increasing.
- exact: total_variation_continuous.
- exact: TV_nondecreasing.
- exact: TV_bounded_variation.
- exact: Lusin_total_variation.
Qed.

End Banach_Zarecki.
