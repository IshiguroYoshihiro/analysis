From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences real_interval.
Require Import esum measure lebesgue_measure numfun (*lebesgue_integral*).
Require Import realfun exp lebesgue_stieltjes_measure derive.

(**md**************************************************************************)
(* # Absolute Continuity                                                      *)
(* ```                                                                        *)
(*   Gdelta (S ; set R) == S is a set of countable intersection of open sets  *)
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
    [/\ (forall i, (B i).1 < (B i).2 /\ `](B i).1, (B i).2[ `<=` `[a, b]),
        trivIset setT (fun i => `](B i).1, (B i).2[%classic) &
        \sum_(k < n) ((B k).2 - (B k).1) < d%:num] ->
    \sum_(k < n) (f (B k).2 - f ((B k).1)) < e%:num.

Lemma total_variation_AC a b (f : R -> R) : a < b ->
  bounded_variation a b f ->
  abs_cont a b (fine \o (total_variation a ^~ f)) -> abs_cont a b f.
Proof.
move=> ab bvH' acH' e.
have := acH' e.
move: (acH') => _.
move=> [d ac'H'].
exists d => n B trivB.
have := ac'H' n B trivB.
move: trivB => [/all_and2[B21 Bab]] trivB sumBd sumHd.
apply: (le_lt_trans _ sumHd).
apply: ler_sum => i _.
have aB1 : a <= (B i).1.
  rewrite leNgt; apply/negP => Bi1a.
  have := Bab i.
  move=> /(_ (((B i).1 + minr a (B i).2)/2)).
  rewrite /= !in_itv/= midf_lt//=; last first.
    by rewrite lt_minr Bi1a B21.
  have H1 : ((B i).1 + minr a (B i).2)%E / 2 < (B i).2.
    rewrite ltr_pdivrMr//.
    rewrite mulr_natr mulr2n.
    rewrite ltr_leD//.
    by rewrite le_minl lexx orbT.
  move=> /(_ H1) /andP[+ _].
  rewrite ler_pdivlMr// mulr_natr mulr2n leNgt => /negP; apply.
  by rewrite ltr_leD// le_minl lexx.
have B2b : (B i).2 <= b.
  rewrite leNgt; apply/negP => Bi2b.
  have := Bab i.
  move=> /(_ ((maxr (B i).1 b + (B i).2)/2)).
  rewrite /= !in_itv/= midf_lt//=; last first.
    by rewrite lt_maxl Bi2b B21.
  rewrite andbT.
  have H1 : (B i).1 < (maxr (B i).1 b + (B i).2)%E / 2.
    rewrite ltr_pdivlMr//.
    rewrite mulr_natr mulr2n.
    rewrite ler_ltD//.
    by rewrite le_maxr lexx.
  move=> /(_ H1) /andP[_].
  rewrite ler_pdivrMr// mulr_natr mulr2n leNgt => /negP; apply.
  by rewrite ler_ltD// le_maxr lexx orbT.
apply: (le_trans (ler_norm (f (B i).2 - f (B i).1))).
rewrite /=.
rewrite (@total_variationD _ a (B i).2 (B i).1 f)//; last first.
  exact: ltW.
rewrite fineD; last 2 first.
- apply/bounded_variationP => //.
  apply: (@bounded_variationl _ _ _ b) => //.
  by rewrite (le_trans _ B2b)// ltW.
- apply/bounded_variationP => //.
    exact: ltW.
  apply: (bounded_variationl _ B2b) => //.
    exact: ltW.
  apply: (bounded_variationr aB1) => //.
  by rewrite (le_trans _ B2b)// ltW.
rewrite addrAC subrr add0r.
rewrite -[leLHS]add0r -ler_subr_addr.
rewrite -lee_fin.
rewrite EFinB.
rewrite fineK; last first.
  apply/bounded_variationP => //.
    exact: ltW.
  apply: (bounded_variationl _ B2b) => //.
    exact: ltW.
  apply: (bounded_variationr aB1) => //.
  by rewrite (le_trans _ B2b)// ltW.
rewrite lee_subr_addr; last first.
  rewrite ge0_fin_numE; last exact: normr_ge0.
  exact: ltry.
rewrite add0e.
apply: total_variation_ge.
exact: ltW.
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
Context (a b : R) (ab : a < b).

Local Notation mu := lebesgue_measure.

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
  mu (\bigcap_i (G_ i)) = \sum_(i \in setT) (mu (G_ i)).
Proof.
Abort.

Lemma Lusin_image_measure0 (f : R -> R) :
{within `[a, b], continuous f} ->
  {in `[a, b]&, {homo f : x y / x <= y}} ->
  lusinN `[a, b] f ->
  exists Z : set R, [/\ Z `<=` `[a, b]%classic,
      compact Z,
      mu Z = 0 &
      mu (f @` Z) = 0].
Proof.
Admitted.

Lemma image_measure0_Lusin (f : R -> R) :
{within `[a, b], continuous f} ->
  {in `[a, b]&, {homo f : x y / x <= y}} ->
  (forall Z : set R, [/\ measurable Z, Z `<=` `[a, b]%classic,
      compact Z,
      mu Z = 0 &
      mu (f @` Z) = 0]) ->
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
have : exists Z, [/\ Z `<=` `[a, b], compact Z, mu Z = 0 & (0 < mu (TV @` Z))%E].
  admit.
move=> [Z [abZ cpt_timZ Z0 ptimZ]].
pose c : R := inf Z.
pose d : R := sup Z.
pose alpha := mu [set (fine \o (total_variation a)^~ f) x | x in Z].
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
  lusinN `[a, b] f ->
  abs_cont a b f.
Proof.
move=> cf incf lf; apply: contrapT => /existsNP[e0] /forallNP fe0.
have {fe0} : forall d : {posnum R},
    exists n, exists B : 'I_n -> R * R,
      [/\ (forall i, (B i).1 < (B i).2 /\ `](B i).1, (B i).2[ `<=` `[a, b]),
          trivIset setT (fun i => `](B i).1, (B i).2[%classic),
          \sum_(k < n) ((B k).2 - (B k).1) < d%:num &
          \sum_(k < n) (f (B k).2 - f (B k).1) >= e0%:num].
  move=> d; have {fe0} := fe0 d.
  move=> /existsNP[n] /existsNP[B] /not_implyP[] [H1 H2 H3 H4].
  by exists n, B; split => //; rewrite leNgt; apply/negP.
move=> /choice[n_0 ab_0].
pose delta_0 (i : nat) : R := (2 ^+ i.+1)^-1.
have d_geo n : delta_0 n = geometric 2^-1 2^-1 n.
  rewrite /geometric /=.
  rewrite /delta_0.
  by rewrite -exprVn exprS.
have d_geo0 : forall k, (0 < k)%N -> (delta_0 k.-1 = geometric 1 (2 ^-1) k).
  rewrite /geometric /=.
  rewrite /delta_0.
  move=> t t0.
  rewrite prednK //.
  by rewrite -exprVn mul1r.
have delta_0_ge0 (i : nat) : 0 < (2 ^+ i.+1)^-1 :> R by rewrite invr_gt0 exprn_gt0.
pose delta_ (i : nat) : {posnum R} := PosNum (delta_0_ge0 i).
pose n_ i := n_0 (delta_ i).
pose ab_ i : 'I_(n_ i) -> R * R := projT1 (cid (ab_0 (delta_ i))).
have d_prop i : \sum_(k < n_ i) (((ab_ i) k).2 - ((ab_ i) k).1) < delta_0 i.
  by rewrite /ab_; case: cid => ? [].
have e0_prop i : \sum_(k < n_ i) (f (((ab_ i) k).2) - f ((ab_ i) k).1) >= e0%:num.
  by rewrite /ab_; case: cid => ? [].
(*have tab_ t : trivIset [set: 'I_(n_ t)]
    (fun i : 'I_(n_ t) => `](ab_ t i).2, (ab_ t i).1[%classic).
  rewrite /ab_; case: cid => ? [_ + _ _]/=.
  rewrite /delta_/=.*)
pose E_ i := \big[setU/set0]_(k < n_ i) `](ab_ i k).2, (ab_ i k).1[%classic.
have mE i: measurable (E_ i) by exact: bigsetU_measurable.
pose G_ i := \bigcup_(j in [set j | (j >= i)%N]) E_ j.
have mG i : measurable (G_ i) by exact: bigcup_measurable.
pose A := \bigcap_i (G_ i).
have Eled : forall n, (mu (E_ n) <= (delta_0 n)%:E)%E.
  move=> t.
  rewrite measure_semi_additive_ord //=; last 2 first.
(*    apply: ltn_trivIset => n2 n1 n12.
    rewrite {2}/Iab; case: Bool.bool_dec; last by rewrite setI0.
    move=> H2.
    rewrite /Iab.
    case: Bool.bool_dec; last by rewrite set0I.
    move=> H1.*)
     admit.
    by apply: bigsetU_measurable => i _.
  apply/ltW.
  under eq_bigr do rewrite lebesgue_measure_itv/= lte_fin.
  (*by apply: d_prop.*) admit.
have mA0 : lebesgue_measure A = 0.
  rewrite /A.
  have H1 : (mu \o G_) x @[x --> \oo] --> mu (\bigcap_n G_ n).
    apply: nonincreasing_cvg_mu => //.
    - move=> /=.
      rewrite (@le_lt_trans _ _ (\sum_(0 <= i <oo) mu (E_ i))%E) //.
        apply: measure_sigma_sub_additive => //; first exact: mG.
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
    - by apply: bigcap_measurable => ? _; apply: mG.
    - move=> s k sk.
      rewrite /G_.
      rewrite subsetEset.
      apply: bigcup_sub => n /= kn.
      apply: bigcup_sup => /=.
      by apply: (@le_trans _ _ k).
  have : (lebesgue_measure \o G_) x @[x --> \oo] --> 0%E.
    rewrite /=.
    have :  (\forall k \near \oo, (cst 0 k <= (mu \o G_) k  <= (delta_0 k.-1)%:E)%E).
      near=> k => /=.
      rewrite measure_ge0 /=.
      apply: (@le_trans _ _ (\big[+%E/0%E]_(k <= j <oo) (mu (E_ j))%E)).
        rewrite (_: G_ k = \bigcup_n G_ (n + k)%N); last first.
        apply/seteqP; split.
        - by exists 0%N => //.
        - apply: bigcup_sub => n _.
          apply: bigcup_sub => j /= nkj.
          apply: bigcup_sup => /=.
          apply: (@leq_trans (n + k)%N) => //.
          exact: leq_addl.
        rewrite (_: (\sum_(k <= j <oo) mu (E_ j))%E = (\sum_(0 <= j <oo) mu (E_ (j + k)%N))%E); last admit.
        apply: measure_sigma_sub_additive.
            by move=> n; apply: mE.
          apply: bigcup_measurable => n _.
          by apply: mG.
        move=> x.
        move=> [/= i _] [j /= ikj Ejx].
        exists (j - k)%N => //.
        rewrite subnK //.
        apply: leq_trans ikj.
        by apply: leq_addl.
      rewrite [leRHS](_:_ = (\big[+%E/0%E]_(k <= j <oo) (delta_0 j)%:E)); last first.
      apply: esym.
      apply: cvg_lim => //.
      rewrite d_geo0; last first.
        near: k.
        by exists 1%N.
      rewrite /geometric /=.
        under eq_cvg => ?.
          under eq_bigr => ? _.
            rewrite /delta_0 -exprVn.
            over.
            rewrite /=.
          over.
        rewrite /=.
        admit.
      by apply: lee_nneseries.
    move/squeeze_cvge.
    apply.
        exact: cvg_cst.
      apply: cvg_trans.
      apply: near_eq_cvg.
      near=> k.
      rewrite d_geo0.
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
have mfA0 : mu (f @` A) = 0.
  (* use lf *)
  apply: lf.
  + rewrite -[X in _ `<=` X](@bigcap_const _ _ (@setT nat) `[a, b]).
    * apply: subset_bigcap => //.
      move=> n _.
      apply: bigcup_sub => j /= nj.
      rewrite /E_.
(*      rewrite bigcup_sup.
      rewrite (_:`[a, b]%classic = \big[setU/set0]_(k < n_ j) `[a, b]%classic).
(*      apply (@subset_bigsetU _ (fun k : `I_(n_ j) => `](ab_ j k).2, (ab_ j k).1[%classic)  (n_ j)).*)*)
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
- exact: Lusin_total_variation.
Qed.

End Banach_Zarecki.
