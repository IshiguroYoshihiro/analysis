(* -*- company-coq-local-symbols: (("`&`" . ?∩) ("`|`" . ?∪) ("set0" . ?∅)); -*- *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
Require Import boolp reals ereal classical_sets signed topology numfun.
Require Import mathcomp_extra functions normedtype.
From HB Require Import structures.
Require Import sequences esum measure fsbigop cardinality set_interval.
Require Import realfun.
Require Import lebesgue_measure lebesgue_integral smeasure.

(******************************************************************************)
(*                     scratch file for Radon-Nikodym                         *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "m1 `<< m2" (at level 51).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma lteNy {R : realDomainType} (x : \bar R) : (x < -oo = false)%E.
Proof. by move: x => []. Qed.

Lemma ltye {R : realDomainType} (x : \bar R) : (+oo < x = false)%E.
Proof. by move: x => []. Qed.

(* TODO: move to classical_sets? *)
Section preimage_bool.
Context d (T : measurableType d).
Implicit Type D : set T.

Lemma preimage_mem_true D : mem D @^-1` [set true] = D.
Proof. by apply/seteqP; split => [x/= /set_mem//|x /mem_set]. Qed.

Lemma preimage_mem_false D : mem D @^-1` [set false] = ~` D.
Proof.
apply/seteqP; split => [x/=|x/=]; last exact: memNset.
by apply: contraFnot; exact/mem_set.
Qed.

End preimage_bool.

(* TODO: move? *)
Lemma fin_num_sume_distrr (R : realType) (I : Type) (s : seq I) r (P : pred I)
    (F : I -> \bar R) : (forall i, P i -> F i \is a fin_num) ->
  (r%:E * (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) (r%:E * F i))%E.
Proof.
move=> PF; elim/big_rec2 : _ => //; first by rewrite mule0.
by move=> i y1 y2 Pi <-; rewrite muleDr// adde_defC fin_num_adde_def// PF.
Qed.

Lemma set_neg_setC T (f : T -> bool) : [set x | ~~ f x] = ~` [set x | f x].
Proof. by apply/seteqP; split => [x/= /negP//|x/= /negP]. Qed.

Lemma set_eq_leq_lt d (X : porderType d) T (f g : T -> X) :
  [set x | f x = g x] = [set x | (f x <= g x)%O] `\` [set x | (f x < g x)%O].
Proof.
apply/seteqP; split => [x/= ->|x []/=]; first by split => //; rewrite ltxx.
by rewrite le_eqVlt => /orP[/eqP ->|].
Qed.

Lemma set_neq_lt d (X : orderType d) T (f g : T -> X) :
  [set x | f x != g x ] = [set x | (f x > g x)%O] `|` [set x | (f x < g x)%O].
Proof.
apply/seteqP; split => [x/=|]; first by rewrite neq_lt => /orP; tauto.
by move=> x/= /orP; rewrite -neq_lt eq_sym.
Qed.

Section set_lt.
Context (R : realType) T (f g : T -> R).

Let E j := [set x | f x - g x >= j.+1%:R^-1].

Lemma set_lt_bigcup :
  [set x | f x > g x] = \bigcup_j E j.
Proof.
apply/seteqP; split => [x/=|x [n _]]; last first.
  by rewrite /E/= -subr_gt0; apply: lt_le_trans; rewrite invr_gt0.
rewrite -subr_gt0 => fgx; exists `|floor (f x - g x)^-1%R|%N => //.
rewrite /E/= -natr1 natr_absz.
rewrite ger0_norm ?floor_ge0 ?invr_ge0; last exact/ltW.
rewrite -[leRHS]invrK lef_pinv//.
- by apply/ltW; rewrite lt_succ_floor.
- by rewrite posrE// ltr_spaddr// ler0z floor_ge0 invr_ge0 ltW.
- by rewrite posrE invr_gt0.
Qed.

End set_lt.

Section eset_lt.
Context (R : realType) T (f g : T -> \bar R).
Local Open Scope ereal_scope.

Let E j := [set x | f x - g x >= j.+1%:R^-1%:E].

Lemma eset_lt_bigcup :
  [set x | f x > g x] = \bigcup_j E j.
Proof.
apply/seteqP; split => [x/=|x [n _]]; last first.
  rewrite /E/= -sube_gt0; apply: lt_le_trans.
  by rewrite lte_fin invr_gt0.
move Hgx : (g x) => gx.
case: gx Hgx => [gx| |].
  move Hfx : (f x) => fx.
  case: fx Hfx => [fx| |].
    move=> Hfx Hgx; rewrite lte_fin -subr_gt0 => fgx.
    exists `|floor (fx - gx)^-1%R|%N => //.
    rewrite /E/= -natr1 natr_absz.
    rewrite ger0_norm ?floor_ge0 ?invr_ge0; last exact/ltW.
    rewrite Hfx Hgx lee_fin.
    rewrite -[leRHS]invrK lef_pinv//.
    - by apply/ltW; rewrite lt_succ_floor.
    - by rewrite posrE// ltr_spaddr// ler0z floor_ge0 invr_ge0 ltW.
    - by rewrite posrE invr_gt0.
  move=> fxoo Hgx _.
  exists 0%N => //.
  rewrite /E/=.
  by rewrite fxoo Hgx// addye// leey.
  by rewrite lteNy.
  by rewrite ltye.
move=> gxoo fxoo.
exists 0%N => //.
by rewrite /E/= gxoo addey// ?leey// -ltNye.
Qed.

End eset_lt.

Section move_to_measure.
Local Open Scope ereal_scope.

Lemma measurable_lt_fun d (X : measurableType d) (R : realType) (f g : X -> \bar R) :
   measurable_fun setT f -> measurable_fun setT g -> measurable [set x | f x < g x].
Proof.
move=> mf mg; under eq_set do rewrite -sube_gt0; rewrite -[X in measurable X]setTI.
by apply : emeasurable_fun_o_infty => //; exact: emeasurable_funB.
Qed.

Lemma measurable_le_fun d (X : measurableType d) (R : realType) (f g : X -> \bar R) :
   measurable_fun setT f -> measurable_fun setT g -> measurable [set x | f x <= g x].
Proof.
move=> mf mg; under eq_set do rewrite leNgt.
by rewrite set_neg_setC; apply measurableC; exact : measurable_lt_fun.
Qed.

Lemma measurable_eq_fun d (X : measurableType d) (R : realType) (f g : X -> \bar R) :
   measurable_fun setT f -> measurable_fun setT g -> measurable [set x | f x = g x].
Proof.
move=> mf mg; rewrite set_eq_leq_lt.
by apply measurableD; [exact : measurable_le_fun|exact : measurable_lt_fun].
Qed.

Lemma measurable_neq_fun d (X : measurableType d) (R : realType) (f g : X -> \bar R) :
   measurable_fun setT f -> measurable_fun setT g -> measurable [set x | f x != g x].
Proof.
by move=> mf mg; rewrite set_neq_lt; apply: measurableU; apply: measurable_lt_fun.
Qed.

Lemma measurable_fun_bigcup d (X : measurableType d) (R : realType)
  (n : nat) (E : (set X)^nat) (mu : {measure set X -> \bar R}) (f : X -> \bar R) :
    (forall i, measurable (E i) /\ measurable_fun (E i) f) ->
     measurable_fun (\bigcup_i E i) f.
Proof.
move=> mfE mE /= Y mY; rewrite setI_bigcupl; apply: bigcup_measurable => i _.
by apply mfE => //; apply mfE.
Qed.

(* NB: this definition is now in master *)
Definition finite_measure d (T : measurableType d) (R : realType)
  (mu : set T -> \bar R) := mu setT < +oo.

Lemma fmuy d (X : measurableType d) (R : realType)
    (mu : {measure set X -> \bar R}) : finite_measure mu ->
  forall E, measurable E -> mu E < +oo.
Proof.
by move=> fmu E mE; rewrite (le_lt_trans _ fmu)// le_measure// inE.
Qed.

End move_to_measure.

(* TODO: move to lebesgue_integral.v? *)
Lemma integrable_abse d (T : measurableType d) (R : realType) D
    (f : T -> \bar R) (mu : {measure set T -> \bar R}) :
  mu.-integrable D f -> mu.-integrable D (abse \o f).
Proof.
move=> [mf foo]; split; first exact: measurable_fun_comp.
by under eq_integral do rewrite abse_id.
Qed.

Lemma integral1 d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (f : T -> \bar R) (A : set T) :
  (forall x, A x -> f x = 0%E) ->
  (\int[mu]_(x in A) f x = 0)%E.
Proof.
by move=> Af0; rewrite (eq_integral (cst 0%E)) ?integral0// => x /[1!inE] /Af0.
Qed.

(* TODO: rename to abs_continuous *)
(* maybe rewrite I : R * R to I : interval R *)
Definition abs_continuous_function (R : realType) (f : R -> R) (I : R * R) :=
  forall e : {posnum R}, exists d : {posnum R},
    forall J : nat -> R * R, forall n : nat,
      \sum_(k < n)((J k).2 - (J k).1) < d%:num ->
        trivIset setT (fun n => `[(J n).1, (J n).2]%classic) ->
          (forall n, I.1 <= (J n).1 /\ (J n).2 <= I.2) ->
            \sum_(k < n) `| f (J k).2 - f (J k).1 | < e%:num.

Local Open Scope ereal_scope.

(* NB: PR in progress *)
Lemma sumeN (R : realType) I r (P : pred I) (f : I -> \bar R) :
  (forall i, P i -> f i \is a fin_num) ->
  (\sum_(i <- r | P i) - f i = - (\sum_(i <- r | P i) f i)).
Proof.
move=> h; elim/big_rec2 : _ => //; first by rewrite oppe0.
by move=> i y1 _ Pi ->; rewrite [in RHS]addeC oppeD ?h// addeC.
Qed.


Section measure_zero.
Local Open Scope ereal_scope.
Variables (d : measure_display) (T : measurableType d) (R : realType).

Definition smzero (A : set T) : \bar R := 0.

Let smzero0 : smzero set0 = 0. Proof. by []. Qed.

Let smzero_isfinite B :measurable B -> smzero B \is a fin_num. Proof. by []. Qed.

HB.instance Definition _ := isSignedMeasure0.Build _ _ _ smzero
  smzero_isfinite.

Let smzero_semi_additive : semi_additive smzero.
move=> F n mF tF mUF.
rewrite /smzero.
by rewrite big1.
Qed.

HB.instance Definition _ :=
  isAdditiveSignedMeasure.Build _ _ _ smzero smzero_semi_additive.

Let smzero_sigma_additive : semi_sigma_additive smzero.
Proof.
move=> F mF tF mUF; rewrite [X in X --> _](_ : _ = cst 0); first exact: cvg_cst.
by apply/funext => n; rewrite big1.
Qed.

HB.instance Definition _ :=
  isSignedMeasure.Build _ _ _ smzero smzero_sigma_additive.

End measure_zero.
Arguments smzero {d T R}.

(*Lemma smsum_mzero (d : _) (T : measurableType d) (R : realType)
    (m_ : {smeasure set T -> \bar R}^nat) :
  smsum m_ 0 = smzero.
Proof. by apply/funext => A/=; rewrite /smsum big_ord0. Qed.*)

Section signed_measure_scale.
Local Open Scope ereal_scope.
Variables (d : measure_display) (T : measurableType d) (R : realType). (* R : realFieldType? *)
Variables (r : R) (m : {smeasure set T -> \bar R}).

Definition smscale (A : set T) : \bar R := r%:E * m A.

Let smscale0 : smscale set0 = 0. Proof. by rewrite /smscale smeasure0 mule0. Qed.

Let smscale_isfinite U : measurable U -> smscale U \is a fin_num.
move=> mU.
apply: fin_numM => //.
by apply: isfinite.
Qed.

HB.instance Definition _ :=
  isSignedMeasure0.Build _ _ _ smscale smscale_isfinite.

Let smscale_semi_additive : semi_additive smscale.
Proof.
move=> F n mF tF mU; rewrite /smscale smeasure_semi_additive//.
by rewrite fin_num_sume_distrr// => i _; rewrite isfinite.
Qed.

HB.instance Definition _ :=
  isAdditiveSignedMeasure.Build _ _ _ smscale smscale_semi_additive.

Let smscale_sigma_additive : semi_sigma_additive smscale.
Proof.
move=> F mF tF mUF; rewrite /smscale; rewrite [X in X --> _](_ : _ =
    (fun n => r%:E * \sum_(0 <= i < n) m (F i))); last first.
  by apply/funext => k; rewrite fin_num_sume_distrr// => n _; rewrite isfinite.
rewrite /mscale; have [->|r0] := eqVneq r 0%R.
  rewrite mul0e [X in X --> _](_ : _ = (fun=> 0)); first exact: cvg_cst.
  by under eq_fun do rewrite mul0e.
by apply: cvgeMl => //; apply: smeasure_semi_sigma_additive.
Qed.

HB.instance Definition _ := isSignedMeasure.Build _ _ _ smscale
  smscale_sigma_additive.

End signed_measure_scale.

Section measure_of_smeasure.
Context d (T : measurableType d) (R : realType).
Variable nu : {smeasure set T -> \bar R}.
Hypothesis nupos : positive_set nu setT.

Definition measure_of_smeasure of positive_set nu setT := nu.
Local Notation mu := (measure_of_smeasure nupos).

Let mu0 : mu set0 = 0. Proof. exact: smeasure0. Qed.

Let mu_ge0 S : measurable S -> 0 <= mu S.
Proof. by move=> mS; have [_ ->//] := nupos; rewrite inE. Qed.

Let mu_sigma_additive : semi_sigma_additive mu.
Proof. exact: smeasure_semi_sigma_additive. Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ (measure_of_smeasure nupos)
  mu0 mu_ge0 mu_sigma_additive.

Lemma measure_of_smeasureE S : mu S = nu S. Proof. by []. Qed.

End measure_of_smeasure.
Arguments measure_of_smeasure {d T R}.

Section absolute_continuity.
Context d (T : measurableType d) (R : realType).
Implicit Types m : set T -> \bar R.

Definition dominates m1 m2 :=
  forall A, measurable A -> m2 A = 0 -> m1 A = 0.

Local Notation "m1 `<< m2" := (dominates m1 m2).

Lemma dominates_trans m1 m2 m3 : m1 `<< m2 -> m2 `<< m3 -> m1 `<< m3.
Proof. by move=> m12 m23 A mA /m23-/(_ mA) /m12; exact. Qed.

End absolute_continuity.
Notation "m1 `<< m2" := (dominates m1 m2).

Lemma subset_nonnegative_set d (R : realType) (X : measurableType d)
  (nu : {smeasure set X -> \bar R}) (N M : set X) : M `<=` N ->
    nu N < 0 -> nu M > 0 -> ~ negative_set nu N -> ~ negative_set nu (N `\` M).
Abort.

(* NB: unused *)
Section positive_set_0.
Context d (X : measurableType d) (R : realType).
Variable nu : {smeasure set X -> \bar R}.
Hypotheses neg_set_0 : forall N, negative_set nu N -> nu N = 0.
Variable S : set X.
Hypothesis mS : measurable S.

Let elt_prop (A : set X * nat * set X) :=
  [/\ measurable A.1.1 /\ A.1.1 `<=` S,
     A.1.2 != 0%N /\ A.1.2%:R^-1%:E <= nu A.1.1 &
     [/\ measurable A.2, A.2 `<=` S & 0 <= nu A.2] ].

Let elt_type := {A : set X * nat * set X | elt_prop A}.

Let F_ (x : elt_type) := (proj1_sig x).1.1.
Let s_ (x : elt_type) := (proj1_sig x).1.2.
Let U_ (x : elt_type) := (proj1_sig x).2.

Let elt_measurable (x : elt_type) : measurable (F_ x).
Proof. by case: x => [[[? ?] ?]] => -[[]]. Qed.

Let elt_FS (x : elt_type) : F_ x `<=` S.
Proof. by case: x => [[[? ?] ?]]; rewrite /F_/= => -[[]]. Qed.

Let elt_s0 (x : elt_type) : s_ x != 0%N.
Proof. by case: x => [[[? ?] ?]]; rewrite /s_/= => -[_ []]. Qed.

Let elt_s_F (x : elt_type) : (s_ x)%:R^-1%:E <= nu (F_ x).
Proof. by case: x => [[[? ?] ?]]; rewrite /s_/F_/= => -[_ []]. Qed.

Let seq_min (a b : elt_type):=
  (forall l B, l != 0%N -> measurable B -> B `<=` S `\` U_ a -> l%:R^-1%:E <= nu B -> (l >= s_ b)%N) /\
  F_ b `<=` S `\` U_ a /\
  U_ b = U_ a `|` F_ b.

Lemma positive_set_0 : nu S >= 0.
Proof.
rewrite leNgt; apply/negP => nuS0.
suff [Fs [mF [FS [tF [spos [nuF smalls]]]]]] :
    {Fs : nat -> set X * nat | let F := fst \o Fs in let s := snd \o Fs in
    (forall n, measurable (F n)) /\
    (forall n, F n `<=` S) /\
    trivIset setT F /\
    (forall n, s n != O) /\
    (forall n, nu (F n) >= (s n)%:R^-1%:E) /\
    (forall n B, measurable B -> B `<=` S `\` \bigcup_i (F i) -> nu B < (s n)%:R^-1%:E) }.
  set F := fst \o Fs; set s := snd \o Fs.
  pose UF := \bigcup_m (F m).
  have mUF : measurable UF by exact: bigcupT_measurable.
  have UFS : UF `<=` S by exact: bigcup_sub.
  have nuUF : nu UF = \sum_(k <oo) nu (F k).
    by apply/esym/cvg_lim => //; exact: smeasure_semi_sigma_additive.
  have lims : (fun n => (s n)%:R : R) --> +oo%R.
    suff : (fun m => (s m)%:R^-1) --> (0 : R)%R.
      by move/gtr0_cvgV0; apply; apply: nearW => // n; rewrite ltr0n lt0n spos.
    apply/(@cvg_series_cvg_0 _ [normedModType R of R^o])/nnseries_is_cvg => //.
    rewrite (@le_lt_trans _ _ (nu UF))// ?ltey_eq ?isfinite// nuUF.
    by apply: lee_nneseries => k _; [rewrite lee_fin|exact: nuF].
  have /neg_set_0 nuSUF : negative_set nu (S `\` UF).
    split; [by rewrite inE; exact: measurableD|move=> G /[1!inE] mG GSF].
    have Gk m : nu G < (s m)%:R^-1%:E.
      by have /smalls : G `<=` S `\` UF by []; exact.
    rewrite -(@fineK _ (nu G)) ?isfinite// lee_fin.
    apply/ler_gtP => _/posnumP[e].
    have [m] : exists m, ((s m)%:R^-1 <= e%:num)%R.
      move/cvgryPge : lims => /(_ e%:num^-1) [N _] /(_ _ (leqnn N)).
      rewrite -(@invrK _ (s N)%:R) ler_pinv; last 2 first.
        by rewrite inE unitfE gt_eqF/=.
        by rewrite inE unitfE invr_gt0 invr_eq0 pnatr_eq0 spos/= ltr0n lt0n.
      by move=> Ne; exists N.
    by apply: le_trans; rewrite -lee_fin fineK ?isfinite// ltW.
  have : nu (S `\` UF) < 0.
    rewrite smeasureD// setIidr// suber_lt0 ?isfinite//.
    rewrite (lt_le_trans nuS0)// nuUF; apply: nneseries_ge0 => k _.
    by rewrite (le_trans _ (nuF k)).
  by rewrite nuSUF ltxx.
have not_neg_set_S : ~ negative_set nu S.
  by move: nuS0 => /[swap] /neg_set_0 ->; rewrite ltxx.
pose s0 := ex_minn (negative_set_bound mS not_neg_set_S).
apply/cid.
have [s00 [F0 [F0S mF0 s0F0]]] : s0 != O /\
    exists F0, [/\ F0 `<=` S, measurable F0 & s0%:R^-1%:E <= nu F0].
  rewrite {}/s0; case: ex_minnP => l /andP[l0 /asboolP[F0 [F0S mF0 lF0]]] Sl.
  by split => //; exists F0.
have nuF00 : 0 <= nu F0 by apply: le_trans s0F0.
have [v [v0 Pv]] : { v : nat -> elt_type |
    v 0%nat = exist _ (F0, s0, F0)
      (And3 (conj mF0 F0S) (conj s00 s0F0) (And3 mF0 F0S nuF00)) /\
    forall n, seq_min (v n) (v n.+1) }.
  apply: dependent_choice_Type.
  move=> [[[F s] U] [[mF FS] [s_neq0 sF] [mU US nuU0]]].
  have not_neg_set_SU : ~ negative_set nu (S `\` U).
    apply: (contra_not (@neg_set_0 (S `\` _))); apply/eqP.
    by rewrite lt_eqF// smeasureD// setIidr// suber_lt0 ?isfinite// (lt_le_trans nuS0).
  have mSU : measurable (S `\` U) by exact: measurableD.
  pose s1 := ex_minn (negative_set_bound mSU not_neg_set_SU).
  apply/cid.
  have [s10 [F1 [F1SU mF1 s1F1]]] : s1 != O /\
    exists F1, [/\ F1 `<=` S `\` U, measurable F1 & s1%:R^-1%:E <= nu F1].
    rewrite {}/s1; case: ex_minnP => l /andP[l0 /asboolP[F2 [F2S mF2 lF2]]] saidai.
    by split => //; exists F2.
  have F1S : F1 `<=` S by apply: (subset_trans F1SU); exact: subDsetl.
  pose UF1 := U `|` F1.
  have mUF1 : measurable UF1 by exact: measurableU.
  have UF1S : UF1 `<=` S by rewrite /UF1 subUset.
  have nuUF1_ge0 : 0 <= nu UF1.
    rewrite smeasureU//; first by rewrite adde_ge0// (le_trans _ s1F1).
    rewrite setIC; apply/disjoints_subset.
    by apply (subset_trans F1SU); exact: subDsetr.
  exists (exist _ (F1, s1, UF1)
    (And3 (conj mF1 F1S) (conj s10 s1F1) (And3 mUF1 UF1S nuUF1_ge0))).
  split => // l B l0 mB BSU lB.
  rewrite /s_ /sval/= /s1.
  case: ex_minnP => m /andP[m0 /asboolP[C [CSU mC mnuC]]] h.
  apply h.
  by apply/andP; split => //; apply/asboolP; exists B; split.
exists (fun n => (proj1_sig (v n)).1) => F s.
split; first by move=> n; exact: elt_measurable.
split; first by move=> n; exact: elt_FS.
have Ubig n : U_ (v n) = \big[setU/set0]_(i < n.+1) F_ (v i).
  elim: n => [|n ih]; first by rewrite v0/= big_ord_recr/= big_ord0 set0U v0.
  by have [_ [_ ->]] := Pv n; rewrite big_ord_recr/= -ih.
split.
  apply: subsetC_trivIset => n /=.
  have [_ [+ _]] := Pv n.
  move/subset_trans; apply.
  rewrite -setTD; apply: setDSS => //.
  by rewrite Ubig big_ord_recr.
split; first by move=> n; exact: elt_s0.
split; first by move=> n; exact: elt_s_F.
move=> n G mG GFS; rewrite ltNge; apply/negP => knG.
have limk : (fun m => (s_ (v m))%:R : R) --> +oo%R.
  suff : (fun m => (s_ (v m))%:R^-1) --> (0 : R)%R.
    move/gtr0_cvgV0; apply; apply: nearW => // m.
    by rewrite lt_neqAle eq_sym pnatr_eq0 elt_s0/= ler0n.
  apply: (@cvg_series_cvg_0 _ [normedModType R of R^o]); apply: nnseries_is_cvg => //.
  pose UF := \bigcup_m F_ (v m).
  have mUF : measurable UF.
    by apply: bigcupT_measurable => i; exact: elt_measurable.
  have nuUF : nu UF = \sum_(k <oo) (nu (F_ (v k))).
    apply/esym/cvg_lim => //.
    apply: (smeasure_semi_sigma_additive (F_ \o v)) => //.
      by move=> i; exact: elt_measurable.
    apply: subsetC_trivIset => i.
    have [_ [+ _]] := Pv i.
    move/subset_trans; apply.
    by rewrite Ubig; exact: subDsetr.
  rewrite (@le_lt_trans _ _ (nu UF))//.
    rewrite nuUF.
    apply: lee_nneseries => k _; [by rewrite lee_fin|].
    exact: elt_s_F.
  by rewrite ltey_eq isfinite.
have [m [nm svnm]] : exists m, (n < m /\ s_ (v n) < s_ (v m))%N.
  move/cvgryPgt : limk => /(_ (s_ (v n))%:R) [m _ Hm].
  exists (n + m.+1)%N.
  by rewrite addnS ltnS leq_addr -(@ltr_nat R) Hm//= -addSn leq_addl.
have {}GFS : G `<=` S `\` \big[setU/set0]_(i < m) (F_ (v i)).
  apply: (subset_trans GFS).
  by apply: setDS; exact: bigsetU_bigcup.
have [+ _] := Pv m.-1.
move/(_ _ _ (elt_s0 (v n)) mG).
rewrite Ubig prednK//; last by rewrite (leq_trans _ nm).
by move=> /(_ GFS knG); rewrite leqNgt svnm.
Qed.

End positive_set_0.

(* NB: unused *)
Lemma positive_set_0_restr d (X : measurableType d) (R : realType) (P : set X)
    (mP : measurable P) (nu : {smeasure set X -> \bar R}) :
  (forall N, measurable N -> negative_set nu (N `&` P) -> smrestr nu mP N = 0) ->
    forall S, S \in measurable -> S `<=` P -> smrestr nu mP S >= 0.
Proof.
move=> h S /[1!inE] mS SP.
pose mu := [the smeasure _ _ of smrestr nu mP].
have : forall N, negative_set mu N -> mu N = 0.
  move=> N [/[1!inE] mN Nmu]; rewrite /mu/= h//; split=> [|E /[1!inE] mE ENP].
    by rewrite inE; exact: measurableI.
  have : E `&` P `<=` N by move=> x [Ex Px]; have [] := ENP x Ex.
  have : measurable (E `&` P) by exact: measurableI.
  rewrite -inE => /Nmu /[apply].
  rewrite /mu/= /smrestr/=.
  suff -> : E `&` P `&` P = E by [].
  rewrite -setIA setIid; apply/seteqP; split=> [x []//|x Ex].
  by have [] := ENP _ Ex.
by move/(@positive_set_0 _ _ _ mu); exact.
Qed.

(*
Lemma measurable_fun_0 d (X : measurableType d) (R : realType) (g : (X -> \bar R)) :
  (fun x : X => \big[maxe/-oo]_(j < 0) g j x) = (fun x : X => \big[maxe/-oo]_(j < 0) g j x)
*)
(* auxiliary lemma *)
(*Lemma F_0 d (X : measurableType d) (R : realType) (g : (X -> \bar R) ^nat) :
  (fun x : X => \big[maxe/-oo]_(j < 0) g j x) = (fun x : X => -oo).
Proof.
apply funext.
move=> x.
by rewrite big_ord0.
Qed.*)

(*Lemma F_step d (X : measurableType d) (R : realType) (g : (X -> \bar R) ^nat) :
  forall n, (fun x : X => \big[maxe/-oo]_(j < n.+1) g j x) =
         (fun x : X => maxe (\big[maxe/-oo]_(j < n) g j x) (g n x)).
Proof.
move=> n.
apply funext.
move=> x.
by apply : big_ord_recr.
Qed.*)

(*
Lemma mkcover_function (T I J : Type) (g : I -> J -> T) (P : T -> Prop ):
  (forall (x : J), exists! (y : I), P (g y x)) ->
    partition setT
      (fun (y : I) => [set x | P (g y x) ]) setT.
Abort.
*)

Lemma integrable_bigcup d (X : measurableType d) (R : realType) (n : nat)
  (E : nat -> set X) (mu : {measure set X -> \bar R}) (f : X -> \bar R) :
    (forall i, measurable (E i) /\ integrable mu (E i) f) ->
                    integrable mu (\bigcup_i (*MN: not genuine bigcup*) E i) f.
Proof.
pose F := (seqDU E).
have disjF : (trivIset [set: nat] F) := (@trivIset_seqDU _ E).
have EF : \bigcup_i E i = \bigcup_i F i := (@seqDU_bigcup_eq _ E).
move=> h.
split.
  apply measurable_fun_bigcup => //.
  move=> i.
  by have [? [? _]] := h i.
rewrite EF.
rewrite ge0_integral_bigcup //.
(* goal 3 ??? *)
(*
have : exists F : nat -> set X, (forall i, (i < n)%nat -> measurable (F i)) /\
                          \bigcup_(i in `I_n) F i = \bigcup_(i in `I_n) E i.
  exists (fun (n : nat) => E n `\` \bigcup_(i in `I_n) E i).
  split.
    move=> i iltn.
    apply measurableD.
      by apply h.
    apply bigcup_measurable => /=.
    move=> k klti.
    apply h.
    by apply (@lt_trans _ _ i).
  rewrite seteqP.
  split.
    by apply subset_bigcup.

  move:h.
  case : n.
    move=> H x.
    move=> H2.
    rewrite /bigcup /=.
    under eq_fun do rewrite ltn0.

    exists 0%nat.
  apply bigcupP.
  move=> bigE.
  rewrite bigcup_set.
  rewrite -inE in bigE.
  have bigE' : (\bigcup_(i in `I_n) E i) = (\bigcup_(i | (i < n)%nat ) E i).
Check (bigcupP bigE).
  move : (bigcupP bigE).
apply (le_lt_trans (\sum_(i in `I_n) (\int[mu]_(x in E i) `|f x|))).
rewrite ge0_integral_bigsetU. *)
Abort.
(* --- *)

Section approxRN.
Context d (X : measurableType d) (R : realType).
Variables mu nu : {measure set X -> \bar R}.

Definition approxRN := [set g : X -> \bar R | [/\
  forall x, 0 <= g x, mu.-integrable setT g &
  forall E, measurable E -> \int[mu]_(x in E) g x <= nu E] ].

Let approxRN_neq0 : approxRN !=set0.
Proof.
exists (cst 0); split => //; first exact: integrable0.
by move=> E mE; rewrite integral0 measure_ge0.
Qed.

Definition int_approxRN := [set \int[mu]_x g x | g in approxRN].

Let int_approxRN_ub : finite_measure nu ->
  exists M, forall x, x \in int_approxRN -> x <= M%:E.
Proof.
move=> nufin; exists (fine (nu setT)) => x.
rewrite inE => -[g [g0 g1 g2] <-{x}].
rewrite fineK; last by rewrite ge0_fin_numE// measure_ge0.
by rewrite (le_trans (g2 setT _))// inE.
Qed.

Definition sup_int_approxRN := ereal_sup int_approxRN.

Local Notation M := sup_int_approxRN.

Definition sup_int_approxRN_ge0 : 0 <= M.
Proof.
rewrite -(ereal_sup1 0) (@le_ereal_sup _ [set 0] int_approxRN)// sub1set inE.
exists (fun=> 0); last exact: integral0.
split => //; first exact : integrable0.
by move=> E; rewrite integral0 => mE; rewrite measure_ge0.
Qed.

Hypothesis nufin : finite_measure nu.

Definition sup_int_approxRN_lty : M < +oo.
Proof.
rewrite /sup_int_approxRN; have [m hm] := int_approxRN_ub nufin.
rewrite (@le_lt_trans _ _ m%:E)// ?ltey// ub_ereal_sup// => x IGx.
by apply: hm; rewrite inE.
Qed.

Definition sup_int_approxRN_fin_num : M \is a fin_num.
Proof.
rewrite ge0_fin_numE//; first exact: sup_int_approxRN_lty.
exact: sup_int_approxRN_ge0.
Qed.

Lemma approxRN_seq_ex : { g : (X -> \bar R)^nat &
  forall m, g m \in approxRN /\ \int[mu]_x (g m x) > M - m.+1%:R^-1%:E }.
Proof.
pose P m g := g \in approxRN /\ M - m.+1%:R^-1%:E < \int[mu]_x g x.
suff : { g : (X -> \bar R) ^nat & forall m, P m (g m)} by case => g ?; exists g.
apply: (@choice _ _ P) => m.
rewrite /P.
have /(@ub_ereal_sup_adherent _ int_approxRN) : (0 < m.+1%:R^-1 :> R)%R.
  by rewrite invr_gt0.
move/(_ sup_int_approxRN_fin_num) => [_ [h Gh <-]].
by exists h; rewrite inE; split => //; rewrite -/M in q.
Qed.

Definition approxRN_seq : (X -> \bar R)^nat := projT1 approxRN_seq_ex.

Local Notation g_ := approxRN_seq.

Lemma approxRN_seq_prop : forall m,
  g_ m \in approxRN /\ \int[mu]_x (g_ m x) > M - m.+1%:R^-1%:E.
Proof. exact: (projT2 approxRN_seq_ex). Qed.

Lemma approxRN_seq_ge0 x n : 0 <= g_ n x.
Proof. by have [+ _]:= approxRN_seq_prop n; rewrite inE /= => -[]. Qed.

Lemma measurable_approxRN_seq n : measurable_fun setT (g_ n).
Proof. by have := approxRN_seq_prop n; rewrite inE /= => -[[_ []]]. Qed.

Definition max_approxRN_seq n x := \big[maxe/-oo]_(j < n.+1) g_ j x.

Local Notation F_ := max_approxRN_seq.

Lemma measurable_max_approxRN_seq n : measurable_fun setT (F_ n).
Proof.
elim: n => [|n ih].
  rewrite /max_approxRN_seq.
  under eq_fun do rewrite big_ord_recr/=; rewrite -/(measurable_fun _ _).
  under eq_fun do rewrite big_ord0; rewrite -/(measurable_fun _ _).
  under eq_fun do rewrite maxNye; rewrite -/(measurable_fun _ _).
  have [+ _] := approxRN_seq_prop 0%N.
  by rewrite inE /= => -[]// _ _ _; exact: measurable_approxRN_seq.
rewrite /max_approxRN_seq => m.
under eq_fun do rewrite big_ord_recr.
by apply : emeasurable_fun_max => //; exact: measurable_approxRN_seq.
Qed.

Lemma max_approxRN_seq_ge0 n x : 0 <= F_ n x.
Proof.
by apply/bigmax_geP; right => /=; exists ord0 => //; exact: approxRN_seq_ge0.
Qed.

Lemma max_approxRN_seq_ge n x : F_ n x >= g_ n x.
Proof. by apply/bigmax_geP; right => /=; exists ord_max. Qed.

Lemma max_approxRN_seq_nd x : nondecreasing_seq (F_ ^~ x).
Proof. by move=> a b ab; rewrite (le_bigmax_ord xpredT (g_ ^~ x)). Qed.

Lemma is_cvg_max_approxRN_seq n : cvg (F_ ^~ n).
Proof. by apply: ereal_nondecreasing_is_cvg; exact: max_approxRN_seq_nd. Qed.

Lemma is_cvg_int_max_approxRN_seq A : measurable A ->
  cvg (fun n => \int[mu]_(x in A) F_ n x).
Proof.
move=> mA; apply: ereal_nondecreasing_is_cvg => a b ab.
apply ge0_le_integral => //.
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- by apply: measurable_funS (measurable_max_approxRN_seq a).
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- exact: measurable_funS (measurable_max_approxRN_seq b).
- by move=> x _; exact: max_approxRN_seq_nd.
Qed.

Definition is_max_approxRN m j := [set x | F_ m x = g_ j x /\
  forall k, (k < j)%N -> g_ k x < g_ j x].

Local Notation E := is_max_approxRN.

Lemma is_max_approxRNE m j : E m j = [set x| F_ m x = g_ j x] `&`
    [set x |forall k, (k < j)%nat -> g_ k x < g_ j x].
Proof. by apply/seteqP; split. Qed.

Lemma trivIset_is_max_approxRN n : trivIset setT (E n).
Proof.
apply/trivIsetP => /= i j _ _ ij.
apply/seteqP; split => // x []; rewrite /E/= => -[+ + [+ +]].
wlog : i j ij / (i < j)%N.
  move=> h Fmgi iFm Fmgj jFm.
  have := ij; rewrite neq_lt => /orP[ji|ji]; first exact: (h i j).
  by apply: (h j i) => //; rewrite eq_sym.
by move=> {}ij Fmgi h Fmgj  => /(_ _ ij); rewrite -Fmgi -Fmgj ltxx.
Qed.

Lemma bigsetU_is_max_approx_RN m : \big[setU/set0]_(j < m.+1) E m j = [set: X].
Proof.
apply/seteqP; split => // x _; rewrite -bigcup_mkord.
pose j := [arg max_(j > @ord0 m) g_ j x]%O.
have j0_proof : exists k, (k < m.+1)%N && (g_ k x == g_ j x).
  by exists j => //; rewrite eqxx andbT.
pose j0 := ex_minn j0_proof.
have j0m : (j0 < m.+1)%N by rewrite /j0; case: ex_minnP => // ? /andP[].
have j0max k : (k < j0)%N -> g_ k x < g_ j0 x.
  rewrite /j0; case: ex_minnP => //= j' /andP[j'm j'j] h kj'.
  rewrite lt_neqAle; apply/andP; split; last first.
    rewrite (eqP j'j) /j; case: arg_maxP => //= i _.
    by move/(_ (Ordinal (ltn_trans kj' j'm))); exact.
  apply/negP => /eqP gkj'.
  have := h k; rewrite -(eqP j'j) -gkj' eqxx andbT (ltn_trans kj' j'm).
  by move=> /(_ erefl); rewrite leqNgt kj'.
exists j0 => //; split.
  rewrite /F_ /max_approxRN_seq (bigmax_eq_arg _ ord0)//; last first.
    by move=> ? _; rewrite leNye.
  rewrite /j0/=; case: ex_minnP => //= j' /andP[j'm /eqP].
  by rewrite /g_ => -> h.
by move=> k kj; exact: j0max.
Qed.

Lemma measurable_is_max_approx_RN m j : measurable (E m j).
Proof.
rewrite is_max_approxRNE; apply measurableI => /=.
  by apply: measurable_eq_fun; [exact: measurable_max_approxRN_seq|
                             exact: measurable_approxRN_seq].
(* TODO : want to use \bigcap_(k < j) [set x | g k x < g j x]) *)
rewrite [T in measurable T](_ : _ = \bigcap_(k in `I_j) [set x | g_ k x < g_ j x]).
  apply bigcap_measurable => k _; apply : measurable_lt_fun => //;
  exact: measurable_approxRN_seq.
by apply/seteqP; split.
Qed.

End approxRN.

Section Radon_Nikodym_finite_ge0.
Context d (X : measurableType d) (R : realType).
Variables mu nu : {measure set X -> \bar R}.
Hypotheses (mufin : finite_measure mu) (nufin : finite_measure nu).

Let G := approxRN mu nu.
Let M := sup_int_approxRN mu nu.
Let g := approxRN_seq mu nufin.
Let F := max_approxRN_seq mu nufin.
Let f := fun x => lim (F ^~ x).

Let mf : measurable_fun setT f.
Proof.
rewrite (_ : f = fun x => lim_esup (F ^~ x)).
  by apply: measurable_fun_lim_esup => // n; exact: measurable_max_approxRN_seq.
by apply/funext=> n; rewrite is_cvg_lim_esupE//; exact: is_cvg_max_approxRN_seq.
Qed.

Let f_ge0 x : 0 <= f x.
Proof.
apply: lime_ge => //; first exact: is_cvg_max_approxRN_seq.
by apply: nearW => ?; exact: max_approxRN_seq_ge0.
Qed.

Let int_fE A : measurable A ->
  \int[mu]_(x in A) f x = lim (fun n => \int[mu]_(x in A) F n x).
Proof.
move=> mA; rewrite monotone_convergence// => n.
- exact: measurable_funS (measurable_max_approxRN_seq mu nufin n).
- by move=> ? ?; exact: max_approxRN_seq_ge0.
- by move=> ?; exact: max_approxRN_seq_nd.
Qed.

Let E m j := is_max_approxRN mu nufin m j.

Let int_F_nu m A (mA : measurable A) : \int[mu]_(x in A) F m x <= nu A.
Proof.
rewrite [leLHS](_ : _ = \sum_(j < m.+1) \int[mu]_(x in (A `&` E m j)) F m x);
    last first.
  rewrite -[in LHS](setIT A) -(bigsetU_is_max_approx_RN mu nufin m) big_distrr/=.
  rewrite (@ge0_integral_bigsetU _ _ _ _ (fun n => A `&` E m n))//.
  - by move=> n; apply: measurableI => //; exact: measurable_is_max_approx_RN.
  - apply: (@measurable_funS _ _ _ _ setT) => //.
    exact: measurable_max_approxRN_seq.
  - by move=> ? ?; exact: max_approxRN_seq_ge0.
  - apply: trivIset_setIl; apply: (@sub_trivIset _ _ _ setT (E m)) => //.
    exact: trivIset_is_max_approxRN.
rewrite [leLHS](_ : _ = \sum_(j < m.+1) (\int[mu]_(x in (A `&` (E m j))) g j x));
    last first.
  apply eq_bigr => i _; apply eq_integral => x; rewrite inE => -[?] [] Fmgi h.
  by apply/eqP; rewrite eq_le; rewrite /F Fmgi lexx.
rewrite [leRHS](_ : _ = \sum_(j < m.+1) (nu (A `&` E m j))); last first.
  rewrite -(@measure_semi_additive _ _ _ nu (fun i => A `&` E m i))//.
  - by rewrite -big_distrr/= bigsetU_is_max_approx_RN// setIT.
  - by move=> k; apply: measurableI => //; exact: measurable_is_max_approx_RN.
  - by apply: trivIset_setIl => //; exact: trivIset_is_max_approxRN.
  - apply: bigsetU_measurable => /= i _; apply: measurableI => //.
    exact: measurable_is_max_approx_RN.
apply: lee_sum => //= i _.
have [+ _] := approxRN_seq_prop mu nufin i.
rewrite inE /G/= => -[_ _]; apply.
by apply: measurableI => //; exact: measurable_is_max_approx_RN.
Qed.

Let F_G m : F m \in G.
Proof.
rewrite inE /G/=; split => //.
- by move=> ?; exact: max_approxRN_seq_ge0.
- split; first exact: measurable_max_approxRN_seq.
  under eq_integral.
    by move=> x _; rewrite gee0_abs; last exact: max_approxRN_seq_ge0; over.
  by have /le_lt_trans := int_F_nu m measurableT; apply.
- by move=> A; exact: int_F_nu.
Qed.

Let M_g_F m : M - m.+1%:R^-1%:E < \int[mu]_x g m x /\
              \int[mu]_x g m x <= \int[mu]_x F m x <= M.
Proof.
split; first by have [] := approxRN_seq_prop mu nufin m.
apply/andP; split.
  apply: ge0_le_integral => //.
  - by move=> x _; exact: approxRN_seq_ge0.
  - exact: measurable_approxRN_seq.
  - by move=> ? *; exact: max_approxRN_seq_ge0.
  - exact: measurable_max_approxRN_seq.
  - by move=> ? _; exact: max_approxRN_seq_ge.
by apply: ereal_sup_ub; exists (F m)  => //; have := F_G m; rewrite inE.
Qed.

Let int_foo : \int[mu]_x `|f x| < +oo.
Proof.
rewrite (@le_lt_trans _ _ M)//; last exact: sup_int_approxRN_lty.
under eq_integral.
  by move=> x _; rewrite gee0_abs; last exact: f_ge0; over.
rewrite int_fE// lime_le//; first exact: is_cvg_int_max_approxRN_seq.
by apply: nearW => n; have [_ /andP[_ ]] := M_g_F n.
Qed.

Let int_f_nu A : measurable A -> \int[mu]_(x in A) f x <= nu A.
Proof.
move=> mA; rewrite int_fE// lime_le //; first exact: is_cvg_int_max_approxRN_seq.
by apply: nearW => n; exact: int_F_nu.
Qed.

Let int_f_M : \int[mu]_x f x = M.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite int_fE// lime_le //; first exact: is_cvg_int_max_approxRN_seq.
  by apply: nearW => n; have [_ /andP[_]] := M_g_F n.
rewrite int_fE//.
have cvgM : (fun m => M - m.+1%:R^-1%:E) --> M.
  rewrite -[X in _ --> X]sube0; apply: cvgeB.
  + by rewrite fin_num_adde_def.
  + exact: cvg_cst.
  + apply/fine_cvgP; split; first exact: nearW.
    rewrite [X in X @ _ --> _](_ : _ = (fun x => x.+1%:R^-1))//.
    apply/gtr0_cvgV0; first exact: nearW.
    apply/cvgrnyP.
    rewrite [X in X @ _](_ : _ = fun n => n + 1)%N; first exact: cvg_addnr.
    by apply/funext => n; rewrite addn1.
have : lim (fun m => M - m.+1%:R^-1%:E) <= lim (fun m => \int[mu]_x F m x).
  apply: lee_lim; [by apply/cvg_ex; exists M|exact: is_cvg_int_max_approxRN_seq|].
  apply: nearW => m.
  by have [/[swap] /andP[? _] /ltW/le_trans] := M_g_F m; exact.
by apply: le_trans; move/cvg_lim : cvgM => ->.
Qed.

Lemma eps_ex A : d.-measurable A -> \int[mu]_(x in A) f x < nu A ->
  { eps : {posnum R} | \int[mu]_(x in A) (f x + eps%:num%:E) < nu A }.
Proof.
move=> mA abs; have [muA0|] := eqVneq (mu A) 0.
  exists (PosNum ltr01).
  under eq_integral.
    move=> x _; rewrite -(@gee0_abs _ (_ + _)); last by rewrite adde_ge0.
    by over.
  rewrite (@integral_abs_eq0 _ _ _ _ setT)//.
    by rewrite (le_lt_trans _ abs)// integral_ge0.
  by apply: emeasurable_funD => //; exact: measurable_fun_cst.
rewrite neq_lt ltNge measure_ge0//= => muA_gt0.
pose mid := ((fine (nu A) - fine (\int[mu]_(x in A) f x)) / 2)%R.
pose e := (mid / fine (mu A))%R.
have ? : \int[mu]_(x in A) f x \is a fin_num.
  rewrite ge0_fin_numE// ?isfinite// ?(lt_le_trans abs)// ?leey//.
  exact: integral_ge0.
have ? : nu A \is a fin_num.
  rewrite ge0_fin_numE//; last exact: measure_ge0.
  by rewrite (le_lt_trans _ nufin)//; apply: le_measure => //; rewrite ?inE.
have e_gt0 : (0 < e)%R.
  rewrite /e divr_gt0//; last by rewrite fine_gt0// fmuy// andbT.
  by rewrite divr_gt0// subr_gt0// fine_lt.
exists (PosNum e_gt0); rewrite ge0_integralD//; last 2 first.
  exact: measurable_funS mf.
  exact: measurable_fun_cst.
rewrite integral_cst// -lte_subr_addr//; last first.
  by rewrite fin_numM// ?ge0_fin_numE ?fmuy// measure_ge0.
rewrite -(@fineK _ (mu A)); last first.
  by rewrite ge0_fin_numE ?fmuy// measure_ge0.
rewrite -EFinM -mulrA mulVr ?mulr1; last first.
  by rewrite unitfE gt_eqF// fine_gt0// muA_gt0// fmuy.
rewrite lte_subr_addl// addeC -lte_subr_addl//; last first.
rewrite -(@fineK _ (nu A))// -[X in _ - X](@fineK _)// -EFinB lte_fin.
by rewrite /mid ltr_pdivr_mulr// ltr_pmulr// ?ltr1n// subr_gt0 fine_lt.
Qed.

Let eps := fun A (mA : d.-measurable A) (h : \int[mu]_(x in A) f x < nu A) =>
  proj1_sig (eps_ex mA h).

Let sigma' A (mA : d.-measurable A) (h : \int[mu]_(x in A) f x < nu A) :=
  fun B => nu B - \int[mu]_(x in B) (f x + (eps mA h)%:num%:E).

Let fin_num_int_f_eps A (mA : d.-measurable A)
    (h : \int[mu]_(x in A) f x < nu A) : forall B, measurable B ->
  \int[mu]_(x in B) (f x + (eps mA h)%:num%:E) \is a fin_num.
Proof.
move=> B mB; rewrite ge0_integralD//; last 2 first.
  exact: measurable_funS mf.
  exact/EFin_measurable_fun/measurable_fun_cst.
rewrite fin_numD integral_cst// fin_numM// ?andbT; last first.
  rewrite ge0_fin_numE ?measure_ge0// (le_lt_trans _ mufin) //.
  by apply: le_measure => //; rewrite inE.
rewrite ge0_fin_numE ?measure_ge0//; last exact: integral_ge0.
rewrite (le_lt_trans _ int_foo)//.
under [in leRHS]eq_integral do rewrite gee0_abs//.
exact: subset_integral.
Qed.

Let fin_num_sigma' A (mA : d.-measurable A) (h : \int[mu]_(x in A) f x < nu A) :
  forall B, measurable B -> sigma' mA h B \is a fin_num.
Proof.
move=> B mB.
rewrite /sigma' fin_numB ge0_fin_numE// ?measure_ge0 //.
rewrite (le_lt_trans _ nufin)/=; first exact: fin_num_int_f_eps.
by apply: le_measure => //; rewrite inE.
Qed.

HB.instance Definition _ A (mA : d.-measurable A) (h : \int[mu]_(x in A) f x < nu A) :=
  @isSignedMeasure0.Build _ _ _ (sigma' mA h) (fin_num_sigma' mA h).

Let sigma'_semi_additive A (mA : d.-measurable A) (h : \int[mu]_(x in A) f x < nu A) :
  semi_additive (sigma' mA h).
Proof.
move=> F' n mF' tF' mUF'.
rewrite /sigma' measure_semi_additive// big_split/= sumeN; last first.
  by move=> i _; rewrite fin_num_int_f_eps.
congr (_ - _); rewrite ge0_integral_bigsetU//.
- rewrite -bigcup_mkord.
  have : measurable_fun setT (fun x => f x + (eps mA h)%:num%:E).
    apply: emeasurable_funD => //.
    exact/EFin_measurable_fun/measurable_fun_cst.
  exact: measurable_funS.
- by move=> x _; rewrite adde_ge0.
- exact: sub_trivIset tF'.
Qed.

HB.instance Definition _ A (mA : d.-measurable A) (h : \int[mu]_(x in A) f x < nu A) :=
  @isAdditiveSignedMeasure.Build _ _ _ (sigma' mA h) (sigma'_semi_additive mA h).

Let sigma'_semi_sigma_additive A (mA : d.-measurable A) (h : \int[mu]_(x in A) f x < nu A) :
  semi_sigma_additive (sigma' mA h).
Proof.
move=> F' mF' tF' mUF'.
rewrite [X in X --> _](_ : _ = (fun n =>
  \sum_(0 <= i < n) nu (F' i) -
  \sum_(0 <= i < n) \int[mu]_(x in F' i) (f x + (eps mA h)%:num%:E))); last first.
  apply/funext => n.
  rewrite big_split/= sumeN// => i _.
  by rewrite fin_num_int_f_eps.
apply: cvgeB.
- rewrite adde_defC fin_num_adde_def//.
  rewrite ge0_fin_numE// ?measure_ge0// (le_lt_trans _ nufin)//.
  apply: le_measure => //.
    by rewrite inE; exact: bigcup_measurable.
  by rewrite inE.
- exact: measure_semi_sigma_additive.
- rewrite (ge0_integral_bigcup mF' _ _ tF').
  + have /cvg_ex[/= l hl] : cvg (fun x =>
        \sum_(0 <= i < x) \int[mu]_(y in F' i) (f y + (eps mA h)%:num%:E)).
      apply: is_cvg_ereal_nneg_natsum => n _.
      by apply: integral_ge0 => x _; rewrite adde_ge0.
    by rewrite (@cvg_lim _ _ _ _ _ _ l).
  + split.
      suff: measurable_fun setT (fun x => f x + (eps mA h)%:num%:E).
        exact: measurable_funS.
      apply: emeasurable_funD => //.
      exact/EFin_measurable_fun/measurable_fun_cst.
    apply: (@le_lt_trans _ _
      (\int[mu]_(x in \bigcup_k F' k) `|f x| +
       \int[mu]_(x in \bigcup_k F' k)`|(eps mA h)%:num%:E|)).
      rewrite -(integralD mUF'); last 2 first.
        * apply: integrable_abse.
          split; first exact: measurable_funS mf.
          rewrite (le_lt_trans _ int_foo)// subset_integral//.
          exact: measurable_fun_comp.
        * apply: integrable_abse.
          split; first exact/EFin_measurable_fun/measurable_fun_cst.
          rewrite integral_cst//= lte_mul_pinfty// (le_lt_trans _ mufin)//.
          by apply: le_measure => //; rewrite inE.
      apply: ge0_le_integral => //.
      * apply: measurable_fun_comp => //.
        apply: emeasurable_funD => //; first exact: measurable_funS mf.
        exact/EFin_measurable_fun/measurable_fun_cst.
      * apply: emeasurable_funD => //.
          apply: measurable_fun_comp => //; first exact: measurable_funS mf.
        apply: measurable_fun_comp => //.
        exact/EFin_measurable_fun/measurable_fun_cst.
      * by move=> x _; exact: lee_abs_add.
    apply: lte_add_pinfty.
      rewrite (le_lt_trans _ int_foo)// subset_integral//.
      exact: measurable_fun_comp.
    rewrite integral_cst//= lte_mul_pinfty// (le_lt_trans _ mufin)//.
    by apply: le_measure => //; rewrite inE.
  + by move=> x _; rewrite adde_ge0.
Qed.

HB.instance Definition _ A (mA : d.-measurable A) (h : \int[mu]_(x in A) f x < nu A) :=
  @isSignedMeasure.Build _ _ _ (sigma' mA h)
    (@sigma'_semi_sigma_additive _ mA h).

Theorem Radon_Nikodym_finite_ge0 : nu `<< mu -> exists f : X -> \bar R,
  [/\ forall x, f x >= 0, mu.-integrable setT f &
      forall E, E \in measurable -> nu E = \int[mu]_(x in E) f x].
Proof.
move=> nu_mu; exists f; split => // A /[!inE] mA.
apply/eqP; rewrite eq_le int_f_nu// andbT leNgt; apply/negP => abs.
pose sigma : {smeasure set X -> \bar R} :=
  [the {smeasure set X -> \bar R} of sigma' mA abs].
have sigmaE : forall F,
    sigma F = nu F - \int[mu]_(x in F) (f x + (eps mA abs)%:num%:E).
  by [].
have [P [N [[mP posP] [mN negN] PNX PN0]]] := Hahn_decomposition sigma.
rewrite !inE in mP mN.
pose AP := A `&` P.
have mAP : measurable AP by exact: measurableI.
have muAP_gt0 : 0 < mu AP.
  rewrite lt_neqAle measure_ge0// andbT eq_sym.
  apply/eqP/(contra_not (nu_mu _ mAP)).
  apply/eqP; rewrite gt_eqF //.
  rewrite (@lt_le_trans _ _ (sigma AP))//.
    apply: (@lt_le_trans _ _ (sigma A)) ; last first.
      rewrite (s_measure_partition2 _ mP mN) // gee_addl //.
      apply: negN => //.
      by rewrite inE; exact: measurableI.
    by rewrite sigmaE sube_gt0// (proj2_sig (eps_ex mA abs)).
  rewrite /sigma/= /sigma' lee_subel_addl.
    by rewrite lee_paddl// integral_ge0// => x _; rewrite adde_ge0.
  rewrite (ge0_fin_numE (measure_ge0 _ _ mAP)) (le_lt_trans _ nufin)//.
  by apply le_measure => //; rewrite inE.
pose h x := if x \in AP then f x + (eps mA abs)%:num%:E else f x.
have mh : measurable_fun setT h.
  apply: (@measurable_fun_if _ _ _ _ _ _ _ _ (mem AP))=> //.
      apply: (@emeasurable_fun_bool _ _ _ _ true).
      by rewrite preimage_mem_true.
    apply: measurable_funTS; apply: emeasurable_funD => //.
    exact: measurable_fun_cst.
  exact: measurable_funTS.
have hge0 x : 0 <= h x by rewrite /h; case: ifPn => // _; rewrite adde_ge0.
have hnuP S : measurable S -> S `<=` AP -> \int[mu]_(x in S) h x <= nu S.
  move=> mS SAP.
  have : sigma S >= 0.
    apply: posP; first  by rewrite inE.
    by apply: (subset_trans SAP); exact: subIsetr.
  rewrite sigmaE sube_ge0; last first.
    apply/orP; right.
    rewrite ge0_fin_numE ?measure_ge0// (le_lt_trans _ nufin)//.
    by apply le_measure => //; rewrite inE.
  apply: le_trans.
  rewrite -{1}(setIid S) integral_mkcondr le_eqVlt; apply/orP; left.
  apply/eqP/eq_integral => x /[!inE] Sx.
  by rewrite /restrict /h !ifT// inE//; exact: SAP.
have hnuN S : measurable S -> S `<=` ~` AP -> \int[mu]_(x in S) h x <= nu S.
  move=> mS ScAP.
  rewrite /h; under eq_integral.
    move=> x xS; rewrite ifF; last first.
      by apply/negbTE; rewrite notin_set; apply: ScAP; apply: set_mem.
    over.
  exact: int_f_nu.
have hnu S : measurable S -> \int[mu]_(x in S) h x <= nu S.
  move=> mS.
  rewrite -(setD0 S) -(setDv AP) setDDr.
  have mSIAP : measurable (S `&` AP) by exact: measurableI.
  have mSDAP : measurable (S `\` AP) by exact: measurableD.
  rewrite integral_setU //; last 2 first.
    - exact: (measurable_funS measurableT).
    - by rewrite disj_set2E setDE setIACA setICl setI0.
  rewrite measureU//.
    by apply: lee_add; [exact: hnuN|exact: hnuP].
  by rewrite setDE setIACA setICl setI0.
have int_h_M : \int[mu]_x h x > M.
  have mCAP := measurableC mAP.
  have disj_AP : [disjoint AP & ~` AP] by exact/disj_set2P/setICr.
  rewrite -(setUv AP) integral_setU ?setUv// /h.
  under eq_integral do rewrite ifT//.
  under [X in _ < _ + X]eq_integral.
    by move=> x; rewrite inE /= => xE0p; rewrite memNset//; over.
  rewrite ge0_integralD//; last 2 first.
    - exact: measurable_funTS.
    - exact: measurable_fun_cst.
  rewrite integral_cst // addeAC -integral_setU ?setUv//.
  rewrite int_f_M -lte_subel_addl; last first.
    by rewrite ge0_fin_numE// ?sup_int_approxRN_lty// sup_int_approxRN_ge0.
  by rewrite /M subee ?mule_gt0// sup_int_approxRN_fin_num.
have Gh : G h.
  split=> //; split => //.
  under eq_integral do rewrite gee0_abs//.
  exact: (le_lt_trans (hnu _ measurableT)).
have : \int[mu]_x h x <= M.
  rewrite -(ereal_sup1 (\int[mu]_x h x)).
  rewrite (@le_ereal_sup _ [set \int[mu]_x h x] (int_approxRN mu nu))//.
  by rewrite sub1set inE; exists h.
by rewrite leNgt int_h_M.
Qed.

End Radon_Nikodym_finite_ge0.

Theorem Radon_Nikodym_sigma_finite_ge0 d (X : measurableType d) (R : realType)
    (mu nu : {measure set X -> \bar R})
    (nufin : finite_measure nu) (musfin : sigma_finite setT mu) :
  nu `<< mu -> exists f : X -> \bar R,
  integrable mu setT f /\ forall E, E \in measurable -> nu E = integral mu E f.
Proof.
(* assume that nu is non-negative *)
move: musfin => [F TF mFAFfin].
have [mF Ffin] := all_and2 mFAFfin.
move: mFAFfin => _.
pose E := seqDU F.
have mE k : measurable (E k).
  by apply: measurableD => //; exact: bigsetU_measurable.
have disj_E := @trivIset_seqDU _ F.
have Efin k : mu (E k) < +oo.
  have mEk : E k \in measurable by rewrite inE.
  rewrite (@le_lt_trans _ _ (mu (F k)))// (le_measure _ mEk)//.
    by rewrite inE.
  exact: subDsetl.
have TE : \bigcup_i E i = setT by rewrite TF [RHS]seqDU_bigcup_eq.
pose mu_ j : {measure set X -> \bar R} := mrestr mu (mE j).
pose nu_ j : {measure set X -> \bar R} := mrestr nu (mE j).
have mu_finite n : finite_measure (mu_ n).
  by rewrite /finite_measure /mu_/= /mrestr setTI Efin.
have nu_finite n : finite_measure (nu_ n).
  rewrite /finite_measure /nu_ /= /mrestr setTI (@le_lt_trans _ _ (nu setT))//.
  by apply: le_measure => //; rewrite inE.
move=> nu_mu.
have nu_mu_ j : nu_ j `<< mu_ j.
  by move=> S mS mu_jS0; apply: nu_mu => //; exact: measurableI.
have [f_tilde Hf_tilde] := choice (fun j =>
  Radon_Nikodym_finite_ge0 (mu_finite j) (nu_finite j) (nu_mu_ j)).
have [f_tilde_ge0 int_f_tildeT int_f_tildeE] := all_and3 Hf_tilde.
rewrite {Hf_tilde}.
pose f_ j x := if x \in E j then f_tilde j x else 0.
have f_ge0 k x : 0 <= f_ k x by rewrite /f_; case: ifP.
have mf_ k : measurable_fun setT (f_ k).
  rewrite /f_.
  apply: (@measurable_fun_if _ _ _ _ _ _ _ _ (mem (E k))) => //.
      apply: (@emeasurable_fun_bool _ _ _ _ true).
      by rewrite preimage_mem_true.
    rewrite preimage_mem_true.
    apply: (measurable_funS measurableT) => //.
    by apply (int_f_tildeT k).
  rewrite preimage_mem_false.
  apply: (measurable_funS measurableT) => //.
  exact: measurable_fun_cst.
have int_f_T k : integrable mu setT (f_ k).
  split=> //.
  under eq_integral do rewrite gee0_abs//.
  rewrite -(setUv (E k)).
  rewrite integral_setU //; last 3 first.
    - exact: measurableC.
    - by rewrite setUv.
    - exact/disj_set2P/subsets_disjoint.
  rewrite /f_.
  under eq_integral do rewrite ifT//.
  rewrite (@eq_measure_integral _ _ _ (E k) (mu_ k)); last first.
    by move=> A mA AEj; rewrite /mu_ /= /mrestr setIidl.
  rewrite -int_f_tildeE ?inE//.
  under eq_integral.
    move=> x.
    rewrite inE /= => nEkx.
    rewrite ifF; last by rewrite memNset.
    over.
  rewrite integral0 adde0.
  rewrite /nu_ /= /mrestr setIid (@le_lt_trans _ _ (nu setT))//.
  by apply: le_measure; rewrite ?inE.
have int_f_E j S : measurable S -> \int[mu]_(x in S) f_ j x = nu (S `&` E j).
  move=> mS.
  have mSIEj := measurableI _ _ mS (mE j).
  have mSDEj := measurableD mS (mE j).
  rewrite -{1}(setUIDK S (E j)).
  rewrite (integral_setU _ mSIEj mSDEj); last 3 first.
    - rewrite setUIDK.
      exact: (measurable_funS measurableT).
    - by move=> x _; exact: f_ge0.
    - by apply/disj_set2P; rewrite setDE setIACA setICr setI0.
  rewrite /f_ -(eq_integral _ (fun x => f_tilde j x)); last first.
    move=> x; rewrite inE => SIEjx.
    by rewrite /f_ ifT// inE; exact: (@subIsetr _ S (E j)).
  rewrite (@eq_measure_integral _ _ _ (S `&` E j) (mu_ j)); last first.
    move=> A mA; rewrite subsetI => -[_ Ejx].
    by rewrite /mu_ /= /mrestr setIidl.
  rewrite -int_f_tildeE; last by rewrite inE; exact: measurableI.
  under eq_integral.
    move=> x.
    rewrite inE setDE /=; move=> [_ nEj].
    rewrite ifF; last by rewrite memNset.
    over.
  rewrite integral0 adde0.
  by rewrite /nu_ /= /mrestr -setIA setIid.
(*
pose f x : \bar R := \esum_(i in [set _ | true]) f_ i x. *)
(* this definition will need less nneseries_esum and proving forall n : nat, true -> 0 <= _
   than use \sum_(j<oo) to define. But we can't do rewrite -nneseries then proved following:
*)
have esum_sum_ge0 (P: nat -> \bar R) : (forall n, 0 <= P n) ->
    \esum_(i in [set _ | true]) P i = \sum_(i <oo) P i.
  by move=> P0;by rewrite nneseries_esum.
pose f x : \bar R := \sum_(j <oo) (f_ j x).
exists f.
have mf : measurable_fun setT f.
  by apply: ge0_emeasurable_fun_sum.
have fge0 : forall x, 0 <= f x.
  move=> x.
  rewrite /f nneseries_esum; last by move=> n _; apply: f_ge0.
  by apply: esum_ge0.
have intfgenu : \int[mu]_x f x = nu setT.
  rewrite integral_nneseries //.
  rewrite nneseries_esum; last by move=> m _; rewrite integral_ge0.
  under eq_esum => /=.
    move=> n _.
    rewrite int_f_E// setTI.
    by over.
  rewrite -nneseries_esum//; last by move=> n; rewrite measure_ge0.
  by rewrite -measure_bigcup // TE.
split.
  split => //.
  under eq_integral => x _.
    rewrite gee0_abs; last exact: nneseries_ge0.
    by over.
  by rewrite intfgenu.
move=> E0; rewrite inE => mE0.
rewrite integral_nneseries//; last first.
  by move=> n; exact: (measurable_funS measurableT).
rewrite nneseries_esum; last first.
  by move=> m _; rewrite integral_ge0.
under eq_esum => /=.
  move=> n _.
  rewrite int_f_E//.
  over.
rewrite -nneseries_esum; last first.
  by move=> n; rewrite measure_ge0//; exact: measurableI.
rewrite -measure_bigcup //; last 2 first.
  - by move=> i; exact: measurableI.
  - by apply: trivIset_setIl; exact: disj_E.
by rewrite -setI_bigcupr TE setIT.
Qed.

(* unused *)
(*
Section measure_of_restricted_signed_measure.
Variables (d : _) (X : measurableType d) (R : realType).
Variable (nu : {smeasure set X -> \bar R}).
Variable (P : set X).

Hypothesis posP : positive_set nu P.

Let mP : measurable P.
Proof. by move: posP => [] mP _;rewrite inE in mP. Qed.

Let nnP : forall E, measurable E -> E `<=` P ->  0 <= nu E.
by move:posP => [] _ H E mE EP; apply: H => //; rewrite inE. Qed.

Definition measure_of_restrsmeasure := smrestr nu mP.

Let nuP0 : measure_of_restrsmeasure set0 = 0.
Proof. by rewrite /measure_of_restrsmeasure /smrestr set0I smeasure0. Qed.

Let nuP_ge0 B :measurable B -> 0 <= measure_of_restrsmeasure B.
Proof.
move=> n.
rewrite /measure_of_restrsmeasure /smrestr.
apply: nnP => //.
by apply measurableI.
Qed.

Let nuP_sigma_additive : semi_sigma_additive measure_of_restrsmeasure.
Proof.
move=> F mF tF mU; pose FP i := F i `&` P.
have mFP i : measurable (FP i) by exact: measurableI.
have tFP : trivIset setT FP.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FP setIACA => ->; rewrite set0I.
rewrite /measure_of_restrsmeasure/smrestr setI_bigcupl; apply: smeasure_semi_sigma_additive => //.
by apply: bigcup_measurable => k _; exact: measurableI.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ measure_of_restrsmeasure
  nuP0 nuP_ge0 nuP_sigma_additive.

End measure_of_restricted_signed_measure.
*)

Section Jordan_decomposition.
Context d (X : measurableType d) (R : realType).
Variable nu : {smeasure set X -> \bar R}.

(* P N mP mNを Hahn_decomposition nuから取り出して一度に全てまとめて定義したい *)
(*
Definition [P [N [[mP posP] [mN negN] PN0 PNT] := Hahn_decomposition nu.
*)

Variables P N : set X.
Hypothesis nuPN : is_Hahn_decomposition nu P N.

Let mP : measurable P.
by have [[mP _] _ _ _] := nuPN ; rewrite inE in mP.
Qed.

Let mN : measurable N.
by have [_ [mN _] _ _] := nuPN; rewrite inE in mN.
Qed.

Definition sjordan_pos : {smeasure set X -> \bar R} := smrestr nu mP.

Definition positive_sjordan_pos : positive_set sjordan_pos setT.
have [posP _ _ _] := nuPN.
split;[|move=> E]; rewrite inE // => mE _.
rewrite /sjordan_pos /smrestr/= /smrestr.
by apply posP; rewrite ?inE; [apply measurableI|apply subIsetr].
Qed.

Definition sjordan_neg : {smeasure set X -> \bar R} := smscale (-1) (smrestr nu mN).

Definition positive_sjordan_neg : positive_set sjordan_neg setT.
Proof.
split; first by rewrite inE.
move=> E /[1!inE]mE _; rewrite /sjordan_neg /= /smscale /= /smrestr muleC mule_le0//.
by move: nuPN => [_ [_ +] _ _] => ->//; rewrite inE; exact: measurableI.
Qed.

Definition jordan_pos : {measure set X -> \bar R} :=
  measure_of_smeasure _ positive_sjordan_pos.

Definition jordan_neg : {measure set X -> \bar R} :=
  measure_of_smeasure _ positive_sjordan_neg.

Lemma finite_jordan_pos : finite_measure jordan_pos.
Proof.
by rewrite /finite_measure /jordan_pos/= /smrestr setTI fin_num_ltey// isfinite.
Qed.

Lemma finite_jordan_neg : finite_measure jordan_neg.
Proof.
rewrite /finite_measure /jordan_neg/= /smscale/= EFinN mulN1e /smrestr setTI.
by rewrite fin_num_ltey// fin_numN isfinite.
Qed.

(* Jordan_measure_decomposition のargumentsがnuだけになるようにしたい*)

(* Lemma nu_dcmp : nu = smeasure_add nu'_p nu'_n. *)

Lemma jordan_decomp A : measurable A -> nu A = jordan_pos A - jordan_neg A.
Proof.
move=> mA; rewrite /= /smscale /= /smrestr /= -[in LHS](setIT A).
case: nuPN => _ _ <- PN0; rewrite setIUr smeasureU//; last 3 first.
  exact: measurableI.
  exact: measurableI.
  by rewrite setIACA PN0 setI0.
by rewrite EFinN mulN1e oppeK.
Qed.

(*
HB.instance Definition _ (E0 : set X) (muE0 : d.-measurable E0)
    (abs : \int[mu]_(x in E0) limF x < nu E0) :=
  @isAdditiveSignedMeasure.Build _ _ _ (sigma' muE0 abs) (sigma'_semi_additive muE0 abs).
*)

End Jordan_decomposition.

(*Section smeasure_sum.
Variables (d : measure_display) (T : measurableType d) (R : realType).
Variables (m : {smeasure set T -> \bar R}^nat) (n : nat).

Variables (mp mn : {measure set T -> \bar R}^nat).

Hypothesis m_dcmp : forall (n : nat) S, measurable S -> m n S = mp n S - mn n S.

Definition smsum (A : set T) : \bar R := \sum_(k < n) m k A.

Let smsum0 : smsum set0 = 0.
Proof.
rewrite /smsum big1 //.
move=> i _.
by apply: smeasure0.
Qed.

Let smsum_isfinite B : measurable B -> smsum B \is a fin_num.
Proof.
move=> mB.
rewrite /smsum.
rewrite fin_numElt.
apply/andP.

have H: \sum_(k < n) m k B = \esum_(k in `I_n) m k B.
  admit.
rewrite H.
under eq_esum => /= i _.
  rewrite (funeposneg (m i)) //.
  
  over.
  split.
Admitted.

HB.instance Definition _ :=
  isSignedMeasure0.Build _ _ _ smsum smsum_isfinite.

Let smsum_semi_additive : semi_additive smsum.
Proof.
Admitted.

HB.instance Definition _ :=
  isAdditiveSignedMeasure.Build _ _ _ smsum smsum_semi_additive.

Let smsum_sigma_additive : semi_sigma_additive smsum.
Proof.
move=> F mF tF mUF.
rewrite [X in _ --> X](_ : _ =
    lim (fun n => \sum_(0 <= i < n) smsum (F i))).
  admit.
rewrite nneseries_sum//. apply: eq_bigr => /= i _.

(* exact: measure_semi_bigcup. *)
Admitted.

HB.instance Definition _ := isSignedMeasure.Build _ _ _ smsum
 smsum_sigma_additive.

End smeasure_sum.

Arguments msum {d T R}.*)

Section smeasure_add.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables m1 m2 : {smeasure set T -> \bar R}.

(*Definition smeasure_add := smsum (fun n => if n is 0%N then m1 else m2) 2.

Lemma smeasure_addE A : smeasure_add A = m1 A + m2 A.
Proof. by rewrite /smeasure_add/= /smsum 2!big_ord_recl/= big_ord0 adde0. Qed.*)

End smeasure_add.

(*
Definition is_Jordan_measure_decomposition d (X : measurableType d) (R : realType)
(nu : {smeasure set X -> \bar R}) (nup nun : {measure set X -> \bar R})
(P N : set X) (HahnPN : is_Hahn_decomposition nu P N) :=
(forall E, measurable E -> nup E = nu (E `&` P))
  /\ (forall E, measurable E -> nun E = nu (E `&` N)).

Definition Jordan_decompositionE d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) (nup nun : {measure set X -> \bar R})
    (P N : set X) (HahnPN : is_Hahn_decomposition nu P N)
    (JordanPN : is_Jordan_measure_decomposition nup nun HahnPN)
:
  nu = smeasure_add (measure_of_smeasure nup) nun.
 *)
(* --- *)

Theorem Radon_Nikodym d (X : measurableType d) (R : realType)
    (mu : {measure set X -> \bar R}) (nu : {smeasure set X -> \bar R})
    (sigma_finite_mu : sigma_finite setT mu) :
  nu `<< mu -> exists f : X -> \bar R,
    integrable mu setT f /\
    forall E, E \in measurable -> nu E = \int[mu]_(x in E) f x.
Proof.
move=> nu_mu.
have [P [N nuPN]] := Hahn_decomposition nu.
have [posP negN _ _] := nuPN.
pose nu_p := jordan_pos nuPN.
pose nu_n := jordan_neg nuPN.
have nu_pdommu : nu_p `<< mu.
  move=> A mA muA0.
  have := nu_mu A mA muA0.
  rewrite (jordan_decomp nuPN)//=.
  rewrite /smrestr/= /smscale/= /smrestr/= EFinN mulN1e oppeK.
  have mAP : measurable (A `&` P).
    apply: measurableI => //.
    by case: posP; rewrite inE.
  have muAP0 : mu (A `&` P) = 0.
    apply/eqP; rewrite eq_le; apply/andP; split.
      by rewrite -muA0 le_measure// inE.
    by rewrite measure_ge0.
  by have -> := nu_mu _ mAP muAP0.
have nu_n_mu : nu_n `<< mu.
  move=> A mA muA0.
  have := nu_mu A mA muA0.
  rewrite (jordan_decomp nuPN)//=.
  rewrite /smrestr/= /smscale/= /smrestr/= EFinN mulN1e oppeK.
  have mAN : measurable (A `&` N).
    apply: measurableI => //.
    by case: negN; rewrite inE.
  have muAN0 : mu (A `&` N) = 0.
    apply/eqP; rewrite eq_le; apply/andP; split.
      by rewrite -muA0 le_measure// inE.
    by rewrite measure_ge0.
  have -> := nu_mu _ mAN muAN0.
  by rewrite oppe0.
(* f_p := Radon_Nikodym_sigma_finite_ge0 nu_pdommu*)
have [f_p [intf_p f_pE]] := Radon_Nikodym_sigma_finite_ge0
  (finite_jordan_pos nuPN) sigma_finite_mu nu_pdommu.
have [f_n [intf_n f_nE]] := Radon_Nikodym_sigma_finite_ge0
  (finite_jordan_neg nuPN) sigma_finite_mu nu_n_mu.
exists (f_p \- f_n); split; first exact: integrableB.
move=> E /[!inE] mE.
rewrite [LHS](jordan_decomp nuPN mE)// integralB//.
- rewrite -f_pE//; last by rewrite inE.
  by rewrite -f_nE//; last by rewrite inE.
- exact: (integrableS measurableT).
- exact: (integrableS measurableT).
Qed.

(* Need lebesgue_stieltjes measure
Proposition abs_continuous_fun_measure d (R : realType)
    (f : R -> R) : forall a b : R,
    abs_continuous_function f (a, b) <-> abs_continuous (hlength f) (@lebesgue_measure d R).
Proof.
Abort.
*)

(* lebesgue_measureのRのTypeが合わない?
Theorem FTC2 d (R : realType) (f : R -> R) (a b : R)
     (f_abscont : abs_continuous_function f (a, b) )
       : exists f' : R -> \bar R, summable `[a, b] f' /\
         {ae (@lebesgue_measure d R), forall x, x \in `[a, b] ->f' x \is a fin_num}
           /\ forall x, x \in `[a, b] ->
                        (f x - f a)%:E = (integral (@lebesgue_measure d R) `[a ,x] f').
Proof.
Abort.
*)

Section integral_ae_eq.
Context d (T : measurableType d) (R : realType) (mu : {measure set T -> \bar R}).

Let integral_measure_lt (g f : T -> \bar R) :
  mu.-integrable setT f -> mu.-integrable setT g ->
  (forall E, measurable E -> \int[mu]_(x in E) f x = \int[mu]_(x in E) g x) ->
  mu [set x | g x < f x] = 0.
Proof.
move=> mf mg fg.
pose E j := [set x | f x - g x >= j.+1%:R^-1%:E].
have mE j : measurable (E j).
  rewrite /E -[X in measurable X]setTI.
  apply: emeasurable_fun_c_infty => //.
  apply: emeasurable_funD => //; first by case: mf.
  by apply: emeasurable_funN => //; case: mg.
have muE j : mu (E j) = 0.
  apply/eqP; rewrite eq_le measure_ge0// andbT.
  have fg0 : \int[mu]_(x in E j) (f \- g) x = 0.
    rewrite integralB//; last 2 first.
      exact: integrableS mf.
      exact: integrableS mg.
    rewrite fg// subee// fin_num_abs (le_lt_trans (le_abse_integral _ _ _))//.
      exact: measurable_funS mg.1.
    case: mg => mg; apply: le_lt_trans.
    by apply: subset_integral => //; exact/measurable_fun_comp.
  have : mu (E j) <= j.+1%:R%:E * \int[mu]_(x in E j) (f \- g) x.
    apply: (@le_trans _ _ ((j.+1%:R)%:E * \int[mu]_(x in E j) j.+1%:R^-1%:E)); last first.
      rewrite lee_pmul//; first exact: integral_ge0.
      apply: ge0_le_integral => //.
        exact: measurable_fun_cst.
        by move=> x; rewrite /E/=; apply: le_trans.
        by apply: emeasurable_funB; [case: mf => + _|case: mg => + _];
          exact: measurable_funS.
    by rewrite integral_cst// muleA -EFinM divrr ?unitfE// mul1e.
  by rewrite fg0 mule0.
have nd_E : {homo E : n0 m / (n0 <= m)%N >-> (n0 <= m)%O}.
  move=> i j ij; apply/subsetPset => x; rewrite /E/=; apply: le_trans.
  by rewrite lee_fin lef_pinv// ?posrE// ler_nat.
rewrite eset_lt_bigcup.
suff: mu (\bigcup_j E j) = 0 by [].
have /cvg_lim h1 : mu \o E --> 0.
  by apply: cvg_near_cst; apply: nearW.
have := @nondecreasing_cvg_mu _ _ _ mu E mE (bigcupT_measurable E mE) nd_E.
move/cvg_lim => h2.
by rewrite -h2// h1.
Qed.

Lemma integral_ae_eq (g f : T -> \bar R) :
  mu.-integrable setT f -> mu.-integrable setT g ->
  (forall E, measurable E -> \int[mu]_(x in E) f x = \int[mu]_(x in E) g x) ->
  ae_eq mu setT f g.
Proof.
move=> mf mg fg.
have mugf : mu [set x | g x < f x] = 0.
  by apply: integral_measure_lt.
have mufg : mu [set x | f x < g x] = 0.
  by apply: integral_measure_lt => // E mE; rewrite fg.
have h : ~` [set x | [set: T] x -> f x = g x] = [set x | f x != g x].
  by apply/seteqP; split => [x/= ?|x/= /eqP]; [apply/eqP; tauto|tauto].
apply/negligibleP.
  by rewrite h; apply: measurable_neq_fun; [case: mf|case: mg].
rewrite h; rewrite set_neq_lt measureU//; last 3 first.
  by apply: measurable_lt_fun; [case: mg|case: mf].
  by apply: measurable_lt_fun; [case: mf|case: mg].
  by apply/seteqP; split => x//=[/lt_trans] => /[apply]; rewrite ltxx.
by rewrite [X in X + _]mugf add0e [LHS]mufg.
Qed.

End integral_ae_eq.
