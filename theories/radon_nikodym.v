(* -*- company-coq-local-symbols: (("`&`" . ?∩) ("`|`" . ?∪) ("set0" . ?∅)); -*- *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
Require Import boolp reals ereal classical_sets signed topology numfun.
Require Import mathcomp_extra functions normedtype.
From HB Require Import structures.
Require Import sequences esum measure fsbigop cardinality set_interval.
Require Import realfun.
Require Import lebesgue_measure lebesgue_integral smeasure. (* lebesgue_stieltjes_measure.*)

(******************************************************************************)
(*                     scratch file for Radon-Nikodym                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma set1Ebigcap {R : realType} (x : R) : [set x] = \bigcap_k `](x - k.+1%:R^-1)%R, x]%classic.
Proof.
apply/seteqP; split => [_ -> k _ /=|].
  by rewrite in_itv/= lexx andbT ltr_subl_addl ltr_addr invr_gt0.
move=> y h; apply/eqP/negPn/negP => yx.
red in h.
simpl in h.
Abort.

Definition abs_continuous d (T : measurableType d) (R : realType)
    (m1 m2 : set T -> \bar R) :=
  forall A : set T, measurable A -> (m2 A = 0)%E -> (m1 A = 0)%E.

Notation "m1 `<< m2" := (abs_continuous m1 m2) (at level 51).

Lemma abs_continuous_trans d (T : measurableType d) (R : realType)
    (m1 m2 m3 : set T -> \bar R) :
  m1 `<< m2 -> m2 `<< m3 -> m1 `<< m3.
Proof. by move=> m12 m23 A mA /m23-/(_ mA) /m12; exact. Qed.

(* maybe rewrite I : R * R to I : interval R *)
Definition abs_continuous_function (R : realType) (f : R -> R) (I : R * R)
    := forall e : {posnum R}, exists d : {posnum R},
         forall J : nat -> R * R, forall n : nat,
           \sum_(k < n)((J k).2 - (J k).1) < d%:num ->
             trivIset setT (fun n => `[(J n).1, (J n).2]%classic) ->
               (forall n, I.1 <= (J n).1 /\ (J n).2 <= I.2 ) ->
                 \sum_(k < n) `| f (J k).2 - f (J k).1 | < e%:num.

Local Open Scope ereal_scope.

Lemma subset_nonnegative_set d (R : realType) (X : measurableType d)
             (nu : {smeasure set X -> \bar R}) (N M : set X) : (M `<=` N) ->
              (nu N < 0)%E -> (nu M > 0)%E -> (~ negative_set nu N) -> (~ negative_set nu (N `\` M)).
Abort.

Section positive_set_0.
Variables (d : _) (X : measurableType d) (R : realType).
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
      by move/invr_cvg0; apply => // n ; rewrite ltr0n lt0n spos.
    apply/(@cvg_series_cvg_0 _ [normedModType R of R^o])/nnseries_is_cvg => //.
    rewrite (@le_lt_trans _ _ (nu UF))// ?ltey_eq ?isfinite// nuUF.
    by apply: lee_nneseries => k _; [rewrite lee_fin|exact: nuF].
  have /neg_set_0 nuSUF : negative_set nu (S `\` UF).
    split; [by rewrite inE; exact: measurableD|move=> G /[1!inE] mG GSF].
    have Gk m : nu G < (s m)%:R^-1%:E.
      by have /smalls : G `<=` S `\` UF by []; exact.
    rewrite -(@fineK _ (nu G)) ?isfinite// lee_fin.
    apply/ler0_addgt0P => _/posnumP[e].
    have [m] : exists m, ((s m)%:R^-1 <= e%:num)%R.
      move/__deprecated__cvgPpinfty : lims => /(_ e%:num^-1) [N _] /(_ _ (leqnn N)).
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
    move/invr_cvg0; apply => // m.
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
  move/__deprecated__cvgPpinfty_lt : limk => /(_ (s_ (v n))%:R) [m _ Hm].
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

Lemma measurable_lt_fun d (X : measurableType d) (R : realType) (f g : X -> \bar R) :
   measurable_fun setT f -> measurable_fun setT g -> measurable [set x | f x < g x].
Proof.
move=> mf mg.
under eq_set do rewrite -sube_gt0.
rewrite -(setTI [set x | 0 < g x - f x]).
apply : emeasurable_fun_o_infty => //.
apply emeasurable_funB => //.
Qed.

Lemma measurable_le_fun d (X : measurableType d) (R : realType) (f g : X -> \bar R) :
   measurable_fun setT f -> measurable_fun setT g -> measurable [set x | f x <= g x].
Proof.
move=> mf mg.
under eq_set do rewrite leNgt.
rewrite (_ : [set _ | _] = ~` [set x | g x < f x]).
  apply measurableC.
  exact : measurable_lt_fun.
apply/seteqP.
split; by move=> x /= /negP.
Qed.

Lemma measurable_eq_fun d (X : measurableType d) (R : realType) (f g : X -> \bar R) :
   measurable_fun setT f -> measurable_fun setT g -> measurable [set x | f x = g x].
Proof.
move=> mf mg.
rewrite (_ : [set x | _ = _] = [set x | f x <= g x] `\` [set x | f x < g x]).
  apply measurableD.
    exact : measurable_le_fun.
  exact : measurable_lt_fun.
apply/seteqP.
split => x /=.
  move=> fg ;split ;rewrite fg;by rewrite ?le_refl ?lt_irreflexive.
move=>[] /=; by rewrite le_eqVlt => /orP[/eqP| ->].
Qed.

(*
Lemma measurable_fun_0 d (X : measurableType d) (R : realType) (g : (X -> \bar R)) :
  (fun x : X => \big[maxe/-oo]_(j < 0) g j x) = (fun x : X => \big[maxe/-oo]_(j < 0) g j x)
*)
(* auxiliary lemma *)
Lemma F_0 d (X : measurableType d) (R : realType) (g : (X -> \bar R) ^nat) :
  (fun x : X => \big[maxe/-oo]_(j < 0) g j x) = (fun x : X => -oo).
Proof.
apply funext.
move=> x.
by rewrite big_ord0.
Qed.

Lemma F_step d (X : measurableType d) (R : realType) (g : (X -> \bar R) ^nat) :
  forall n, (fun x : X => \big[maxe/-oo]_(j < n.+1) g j x) =
         (fun x : X => maxe (\big[maxe/-oo]_(j < n) g j x) (g n x)).
Proof.
move=> n.
apply funext.
move=> x.
by apply : big_ord_recr.
Qed.

(*
Lemma mkcover_function (T I J : Type) (g : I -> J -> T) (P : T -> Prop ):
  (forall (x : J), exists! (y : I), P (g y x)) ->
    partition setT
      (fun (y : I) => [set x | P (g y x) ]) setT.
Abort.
*)

Lemma measurable_fun_bigcup d (X : measurableType d) (R : realType)
  (n : nat) (E : nat -> set X) (mu : {measure set X -> \bar R})
    (f : X -> \bar R) : (forall i, measurable (E i) /\ measurable_fun (E i) f) ->
                          measurable_fun (\bigcup_i E i) f.
Proof.
move=> mfE mE /= Y mY.
rewrite setI_bigcupl.
apply bigcup_measurable.
move=> i iltn.
apply mfE => //.
by apply mfE.
Qed.

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


Section emeasurable_fun.
Local Open Scope ereal_scope.
Context d (T : measurableType d).
Implicit Types (D : set T).

(* PR *)
Lemma emeasurable_fun_bool (D : set T) (f : T -> bool) b :
  measurable (f @^-1` [set b]) -> measurable_fun D f.
Proof.
have FNT : [set false] = [set~ true] by apply/seteqP; split => -[]//=.
wlog {b}-> : b / b = true.
case: b => [|h]; first exact.
by rewrite FNT -preimage_setC => /measurableC; rewrite setCK; exact: h.
move=> mfT mD /= Y; have := @subsetT _ Y; rewrite setT_bool => YT.
have [-> _|-> _|-> _ |-> _] := subset_set2 YT.
      by rewrite preimage0 ?setI0.
    by apply: measurableI => //; exact: mfT.
  rewrite -[X in measurable X]setCK; apply: measurableC; rewrite setCI.
  apply: measurableU; first exact: measurableC.
by rewrite FNT preimage_setC setCK; exact: mfT.
by rewrite -setT_bool preimage_setT setIT.
Qed.

Lemma in_mem_mem_true (D : set T) : in_mem^~ (mem D) @^-1` [set true] = D.
Proof.
rewrite/preimage.
apply/seteqP.
split => x /=.
  by move/set_mem.
by move/mem_set.
Qed.

Lemma in_mem_mem_false (D : set T) : in_mem^~ (mem D) @^-1` [set false] = ~` D.
Proof.
rewrite /preimage.
apply/seteqP.
split.
  move=> x /=.
  apply: contraFnot.
  by rewrite inE.
move=> x /=.
by apply: memNset.
Qed.

End emeasurable_fun.

Section RN_approx.
Context d (X : measurableType d) (R : realType) (mu nu : {measure set X -> \bar R}).

Definition RN_approx := [set g : X -> \bar R | [/\
  forall x, g x >= 0, integrable mu setT g &
  forall E, E \in measurable -> \int[mu]_(x in E) g x <= nu E] ]%E.

(* NB: used in this section only? *)
Definition RN_approx_neq0 : RN_approx !=set0.
Proof.
exists (cst 0%E); split; first by [].
- exact: integrable0.
- by move=> E;rewrite inE => mE; rewrite integral0 measure_ge0.
Qed.

Definition RN_approx_integral := [set \int[mu]_x g x | g in RN_approx]%E.

(* NB: useless? *)
Definition RN_approx_integral_neq0 : RN_approx_integral !=set0.
Proof.
have [g [g0 g1 g2]] := RN_approx_neq0.
by exists (\int[mu]_x g x)%E, g.
Qed.

(* NB: used in this section only? *)
Definition RN_approx_integral_ub (nufinite : (nu setT < +oo)%E) :
  exists M, forall x, x \in RN_approx_integral -> (x <= M%:E)%E.
Proof.
exists (fine (nu setT)) => x.
rewrite inE => -[g [g0 g1 g2] <-{x}].
rewrite fineK; last first.
  by rewrite ge0_fin_numE// measure_ge0.
by rewrite (le_trans (g2 setT _))// inE.
Qed.

Definition sup_RN_approx_integral := ereal_sup RN_approx_integral.

Definition sup_RN_approx_integral_ge0 : 0 <= sup_RN_approx_integral.
Proof.
rewrite -(ereal_sup1 0).
apply (@le_ereal_sup _ [set 0] RN_approx_integral).
rewrite sub1set inE.
exists (fun x => 0%E); last first.
  exact: integral0.
split => //.
  exact : integrable0.
move=> E.
by rewrite integral0 inE => mE; rewrite measure_ge0.
Qed.

Definition sup_RN_approx_integral_lty (nufinite : (nu setT < +oo)%E) :
  sup_RN_approx_integral < +oo.
Proof.
rewrite /sup_RN_approx_integral.
move: (RN_approx_integral_ub nufinite).
move=> [m] IGbound'.
apply : (@le_lt_trans _ _ m%:E); last by rewrite ltey.
apply ub_ereal_sup.
move=> x IGx.
apply IGbound'.
by rewrite inE.
Qed.

Definition sup_RN_approx_integral_fin_num (nufinite : (nu setT < +oo)%E) :
  sup_RN_approx_integral \is a fin_num.
Proof.
rewrite ge0_fin_numE//.
exact: sup_RN_approx_integral_lty.
exact: sup_RN_approx_integral_ge0.
Qed.

Lemma RN_approx_sequence_ex (nufinite : (nu setT < +oo)%E) : { g : (X -> \bar R)^nat |
  forall m, g m \in RN_approx /\
    \int[mu]_x (g m x) > sup_RN_approx_integral - m.+1%:R^-1%:E }.
Proof.
pose P (m: nat) (g : X -> \bar R) := g \in RN_approx /\
  sup_RN_approx_integral - (m.+1%:R^-1)%:E < \int[mu]_x g x.
suff : { g : (X -> \bar R) ^nat & forall m : nat, P m (g m)}.
  by case => g Hg; exists g.
apply choice => m.
rewrite /P.
have /(@ub_ereal_sup_adherent _ RN_approx_integral) : (0 < m.+1%:R^-1 :> R)%R by rewrite invr_gt0.
move/(_ (sup_RN_approx_integral_fin_num nufinite)) => [_ [h Gh <-]].
by exists h; rewrite inE; split => //; rewrite -/M in q.
Qed.

Definition RN_approx_sequence (nufinite : (nu setT < +oo)%E) : (X -> \bar R)^nat :=
  proj1_sig (RN_approx_sequence_ex nufinite).

Lemma RN_approx_sequence_prop (nufinite : (nu setT < +oo)%E) : forall m,
  RN_approx_sequence nufinite m \in RN_approx /\
  \int[mu]_x (RN_approx_sequence nufinite m x) > sup_RN_approx_integral - m.+1%:R^-1%:E.
Proof. exact: (proj2_sig (RN_approx_sequence_ex nufinite)). Qed.

Lemma RN_approx_sequence_ge0 (nufinite : (nu setT < +oo)%E) x n :
  0 <= RN_approx_sequence nufinite n x.
Proof.
by have [+ _]:= RN_approx_sequence_prop nufinite n; rewrite inE /= => -[].
Qed.

Lemma measurable_RN_approx_sequence (nufinite : (nu setT < +oo)%E) n :
  measurable_fun setT (RN_approx_sequence nufinite n).
Proof.
have := RN_approx_sequence_prop nufinite n.
by rewrite inE /= => -[[_ []]].
Qed.

Definition max_RN_approx_sequence (nufinite : (nu setT < +oo)%E) (m : nat) (x : X) :=
  \big[maxe/-oo]_(j < m.+1) RN_approx_sequence nufinite j x.

Lemma measurable_max_RN_approx_sequence (nufinite : (nu setT < +oo)%E) n :
  measurable_fun setT (max_RN_approx_sequence nufinite n).
Proof.
induction n.
  rewrite /max_RN_approx_sequence.
  under eq_fun do rewrite big_ord_recr/=; rewrite -/(measurable_fun _ _).
  under eq_fun do rewrite big_ord0; rewrite -/(measurable_fun _ _).
  under eq_fun do rewrite maxNye; rewrite -/(measurable_fun _ _).
  have [+ _] := RN_approx_sequence_prop nufinite 0%N.
  rewrite inE /= => -[]// _ _ _.
  exact: measurable_RN_approx_sequence.
rewrite /max_RN_approx_sequence.
move=> m.
under eq_fun do rewrite big_ord_recr.
by apply : emeasurable_fun_max => //; exact: measurable_RN_approx_sequence.
Qed.

End RN_approx.

(* TODO: rename? really useful? *)
Lemma muE0oo d (X : measurableType d) (R : realType)
  (mu : {measure set X -> \bar R}) (mufinite : (mu setT < +oo)%E)
  : forall E0 : set X, d.-measurable E0 ->
  mu E0 < +oo.
Proof.
move=> E0 mE0.
by rewrite (le_lt_trans _ mufinite)// le_measure// inE.
Qed.

(* TODO: PR? not already there? *)
Lemma sumeN (R : realType) I r (P : pred I) (f : I -> \bar R) :
  (forall i, P i -> f i \is a fin_num) ->
  (\sum_(i <- r | P i) - f i = - (\sum_(i <- r | P i) f i)).
Proof.
move=> h; elim/big_rec2 : _ => //; first by rewrite oppe0.
by move=> i y1 _ Pi ->; rewrite [in RHS]addeC oppeD ?h// addeC.
Qed.

Section Radon_Nikodym_finite_ge0.
Variables (d : _) (X : measurableType d) (R : realType).
Variables (mu nu : {measure set X -> \bar R}).
Hypotheses (mufinite : (mu setT < +oo)%E) (nufinite : (nu setT < +oo)%E).

(* maybe define G : set R insted of set \bar R
pose G' := [set g : X -> \bar R |
            [/\ (forall x, (g x >= 0)%E),
               integrable mu setT g &
                 forall E, E \in measurable -> fine (\int[mu]_(x in E) g x) <= fine (nu E) ] ].
*)

Let G := RN_approx mu nu.

Let IG := RN_approx_integral mu nu.

Let M := sup_RN_approx_integral mu nu.

Let g := RN_approx_sequence mu nufinite.

Let F := max_RN_approx_sequence mu nufinite.

Let F_ge0 m x : 0 <= F m x.
Proof.
apply/bigmax_geP; right => /=; exists ord0 => //.
exact: RN_approx_sequence_ge0.
Qed.

Let Fgeqg m x : F m x >= g m x.
Proof.
by apply/bigmax_geP; right => /=; exists ord_max.
Qed.

Let nd_F x : nondecreasing_seq (F ^~ x).
Proof.
by move=> a b ab; rewrite /F (le_bigmax_ord xpredT (g ^~ x)).
Qed.

Let is_cvg_F n : cvg (F ^~ n).
Proof.
by apply: ereal_nondecreasing_is_cvg; exact: nd_F.
Qed.

Let limF := fun x => lim (F^~ x).

Let mlimF : measurable_fun setT limF.
Proof.
rewrite (_ : limF = fun x => elim_sup (F ^~ x)).
  by apply: measurable_fun_lim_esup => // n; exact: measurable_max_RN_approx_sequence.
by apply/funext => n; rewrite /limF is_cvg_elim_supE.
Qed.

Let limF_ge0 x : 0 <= limF x.
Proof.
by apply: __deprecated__ereal_lim_ge => //; exact: nearW.
Qed.

Let int_limFE E0 : measurable E0 ->
    \int[mu]_(x in E0) limF x = lim (fun n : nat => \int[mu]_(x in E0) F n x).
Proof.
move=> mE0; rewrite monotone_convergence//.
by move=> n; apply: measurable_funS (measurable_max_RN_approx_sequence mu nufinite n).
Qed.

Let is_cvg_int_F E0 : measurable E0 -> cvg (fun n => \int[mu]_(x in E0) F n x).
Proof.
move=> mE0; apply: ereal_nondecreasing_is_cvg => a b ab.
by apply ge0_le_integral => //; [exact: measurable_funS (measurable_max_RN_approx_sequence mu nufinite a) |
  exact: measurable_funS (measurable_max_RN_approx_sequence mu nufinite b) | by move=> x _; exact: nd_F].
Qed.

Let E m j := [set x | F m x = g j x /\ forall k, (k < j)%N -> g j x > g k x].

Let hE m j x : E m j x -> forall k : 'I_m.+1, (k >= j)%N -> g j x >= g k x.
Proof.
move=> -[Fmgj h] k; rewrite leq_eqVlt => /orP[/eqP ->//|jk].
rewrite leNgt; apply/negP => gjk.
have : F m x > g j x by apply/bigmax_gtP => /=; right; exists k.
by rewrite Fmgj ltxx.
Qed.

Let E_setI m j : E m j = [set x| F m x = g j x] `&`
    [set x |forall k, (k < j)%nat -> g k x < g j x].
Proof.
by apply/seteqP; split.
Qed.

Let tE m : trivIset setT (E m).
Proof.
apply/trivIsetP => /= i j _ _ ij.
apply/seteqP; split => // x []; rewrite /E/= => -[+ + [+ +]].
wlog : i j ij / (i < j)%N.
  move=> h Fmgi iFm Fmgj jFm.
  have := ij; rewrite neq_lt => /orP[ji|ji]; first exact: (h i j).
  by apply: (h j i) => //; rewrite eq_sym.
by move=> {}ij Fmgi h Fmgj  => /(_ _ ij); rewrite -Fmgi -Fmgj ltxx.
Qed.

Let XE m : [set: X] = \big[setU/set0]_(j < m.+1) E m j.
Proof.
apply/seteqP; split => // x _; rewrite -bigcup_mkord.
(* TODO: fix arg max notation spacing *)
pose j := [arg max_(j > @ord0 m) g j x]%O.
have j0_proof : exists k, (k < m.+1)%N && (g k x == g j x).
  by exists j => //; rewrite eqxx andbT.
pose j0 := ex_minn j0_proof.
have j0m : (j0 < m.+1)%N by rewrite /j0; case: ex_minnP => // ? /andP[].
have j0max k : (k < j0)%N -> g k x < g j0 x.
  rewrite /j0; case: ex_minnP => //= j' /andP[j'm j'j] h kj'.
  rewrite lt_neqAle; apply/andP; split; last first.
    rewrite (eqP j'j) /j; case: arg_maxP => //= i _.
    by move/(_ (Ordinal (ltn_trans kj' j'm))); exact.
  apply/negP => /eqP gkj'.
  have := h k; rewrite -(eqP j'j) -gkj' eqxx andbT (ltn_trans kj' j'm).
  by move=> /(_ erefl); rewrite leqNgt kj'.
exists j0 => //; split.
  rewrite /F /max_RN_approx_sequence (bigmax_eq_arg _ ord0)//; last by move=> ? _; rewrite leNye.
  by rewrite /j0; case: ex_minnP => //= j' /andP[j'm /eqP -> h].
by move=> k kj; exact: j0max.
Qed.

Let measurable_E m j : measurable (E m j).
Proof.
rewrite E_setI; apply measurableI => /=.
  by apply: measurable_eq_fun; [exact: measurable_max_RN_approx_sequence|exact: measurable_RN_approx_sequence].
(* TODO : want to use \bigcap_(k < j) [set x | g k x < g j x]) *)
rewrite [T in measurable T](_ : _ = \bigcap_(k in `I_j) [set x | g k x < g j x]).
  by apply bigcap_measurable => k _; apply : measurable_lt_fun; exact : measurable_RN_approx_sequence.
by apply/seteqP; split.
Qed.

Let Fleqnu m E0 (mE : measurable E0) : \int[mu]_(x in E0) F m x <= nu E0.
Proof.
have -> : \int[mu]_(x in E0) F m x = \sum_(j < m.+1) \int[mu]_(x in (E0 `&` (E m j))) F m x.
  rewrite -[in LHS](setIT E0) (XE m) big_distrr/=.
  rewrite (@ge0_integral_bigsetU _ _ _ _ (fun n => E0 `&` E m n))//.
  - by move=> n; exact: measurableI.
  - by apply: (@measurable_funS _ _ _ _ setT) => //; exact: measurable_max_RN_approx_sequence.
  apply: trivIset_setI.
  by apply: (@sub_trivIset _ _ _ setT (fun i => E m i)) => //.
have -> : \sum_(j < m.+1) (\int[mu]_(x in (E0 `&` (E m j))) F m x) =
          \sum_(j < m.+1) (\int[mu]_(x in (E0 `&` (E m j))) g j x).
  apply eq_bigr => i _; apply eq_integral => x; rewrite inE => -[?] [] Fmgi h.
  by apply/eqP; rewrite eq_le; rewrite Fmgi lexx.
have <- : \sum_(j < m.+1) (nu (E0 `&` (E m j))) = nu E0.
  rewrite -(@measure_semi_additive _ _ _ nu (fun i => E0 `&` E m i))//.
  - by rewrite -big_distrr/= -XE// setIT.
  - by move=> k; exact: measurableI.
  - exact: trivIset_setI.
  - by apply: bigsetU_measurable => /= i _; exact: measurableI.
apply: lee_sum => //= i _.
have [+ _] := RN_approx_sequence_prop mu nufinite i.
rewrite inE /G/= => -[_ _].
apply.
by rewrite inE; exact: measurableI.
Qed.

Let FminG m : F m \in G.
Proof.
rewrite inE /G/=; split => //.
- split; first exact: measurable_max_RN_approx_sequence.
  under eq_integral.
    by move=> x _; rewrite gee0_abs; last exact: F_ge0; over.
  by have /le_lt_trans := Fleqnu m measurableT; apply.
- by move=> E0; rewrite inE; exact: Fleqnu.
Qed.

Let H3 m :  M - (m.+1%:R^-1)%:E < \int[mu]_x g m x /\
             \int[mu]_x g m x <= \int[mu]_x F m x <= M.
Proof.
split; first by have [] := RN_approx_sequence_prop mu nufinite m.
apply/andP; split.
  apply: ge0_le_integral => //.
  - by move=> x _; exact: RN_approx_sequence_ge0.
  - exact: measurable_RN_approx_sequence.
  - exact: measurable_max_RN_approx_sequence.
apply: ereal_sup_ub; exists (F m) => //.
by have := FminG m; rewrite inE.
Qed.

Let limFoo : \int[mu]_x `|limF x| < +oo.
Proof.
rewrite (@le_lt_trans _ _ M)//; last first.
  exact: sup_RN_approx_integral_lty.
under eq_integral.
  by move=> x _; rewrite gee0_abs; last exact: limF_ge0; over.
rewrite int_limFE// __deprecated__ereal_lim_le//; first exact: is_cvg_int_F.
by apply: nearW => n; have [_ /andP[_ ]] := H3 n.
Qed.

Let limFleqnu E0 : measurable E0 -> \int[mu]_(x in E0) limF x <= nu E0.
Proof.
move=> mE0; rewrite int_limFE// __deprecated__ereal_lim_le //; first exact: is_cvg_int_F.
by apply: nearW => n; exact: Fleqnu.
Qed.

Let limFXeqM : \int[mu]_x limF x = M.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite int_limFE// __deprecated__ereal_lim_le //; first exact: is_cvg_int_F.
  by apply: nearW => n; have [_ /andP[_]] := H3 n.
rewrite int_limFE//.
have Htmp : (fun m => M - (m.+1%:R^-1)%:E) --> M.
  rewrite -[X in _ --> X]sube0.
  apply: __deprecated__ereal_cvgB.
  + by rewrite fin_num_adde_def.
  + exact: cvg_cst.
  + apply/__deprecated__ereal_cvg_real; split; first by apply: nearW.
    rewrite [X in X --> _](_ : _ = (fun x => (x.+1%:R^-1))) //.
    apply/invr_cvg0 => //.
    apply/cvgrnyP.
    rewrite [X in X @ _](_ : _ = (fun n => n + 1)%N).
      by apply:cvg_addnr.
    by apply/funext => n; rewrite addn1.
have : lim (fun m => M - (m.+1%:R^-1)%:E) <= lim (fun m => \int[mu]_x F m x).
  apply: lee_lim.
  - by apply/cvg_ex; exists M.
  - exact: is_cvg_int_F.
  - apply: nearW => m.
    by have [/[swap] /andP[? _] /ltW/le_trans] := H3 m; exact.
by apply: le_trans; move/cvg_lim : Htmp => ->.
Qed.

Lemma eps_construction : forall E0 : set X, d.-measurable E0 ->
  \int[mu]_(x in E0) limF x < nu E0 ->
  { eps : {posnum R} | \int[mu]_(x in E0) (limF x + eps%:num%:E) < nu E0 }.
Proof.
move=> E0 mE0 abs.
have [muE0_eq0|] := eqVneq (mu E0) 0.
  exists (PosNum ltr01).
  under eq_integral.
    move=> x _.
    rewrite -(@gee0_abs _ (_ + _)); last first.
      by rewrite adde_ge0.
    over.
  rewrite (@integral_abs_eq0 _ _ _ _ setT)//.
    by rewrite (le_lt_trans _ abs)// integral_ge0//.
  apply: emeasurable_funD => //.
  exact: measurable_fun_cst.
rewrite neq_lt ltNge measure_ge0//= => muE0_gt0.
pose mid := ((fine (nu E0) - fine (\int[mu]_(x in E0) limF x)) / 2)%R.
pose e := (mid / fine (mu E0))%R.
have ? : \int[mu]_(x in E0) limF x \is a fin_num.
  rewrite ge0_fin_numE// ?isfinite// ?(lt_le_trans abs)// ?leey//.
  exact: integral_ge0.
have ? : nu E0 \is a fin_num.
  rewrite ge0_fin_numE//.
    rewrite (le_lt_trans _ nufinite)//.
    by apply: le_measure => //; rewrite ?inE.
  by apply: measure_ge0.
have e_gt0 : (0 < e)%R.
  rewrite /e divr_gt0//; last by rewrite fine_gt0// muE0oo// andbT.
  by rewrite divr_gt0// subr_gt0// fine_lt.
exists (PosNum e_gt0); rewrite ge0_integralD//; last 2 first.
  exact: measurable_funS mlimF.
  exact: measurable_fun_cst.
rewrite integral_cst// -lte_subr_addr//; last first.
  rewrite fin_numM// ?ge0_fin_numE//.
    by rewrite muE0oo.
  by apply: measure_ge0.
rewrite -(@fineK _ (mu E0)); last first.
  rewrite ge0_fin_numE.
    by rewrite muE0oo.
  by rewrite measure_ge0.
rewrite -EFinM -mulrA mulVr ?mulr1; last first.
  by rewrite unitfE gt_eqF// fine_gt0// muE0_gt0// muE0oo.
rewrite lte_subr_addl// addeC -lte_subr_addl//; last first.
rewrite -(@fineK _ (nu E0))//.
rewrite -[X in _ - X](@fineK _)//.
rewrite -EFinB lte_fin /mid ltr_pdivr_mulr// ltr_pmulr// ?ltr1n//.
by rewrite subr_gt0 fine_lt.
Qed.

Let eps := fun (E0 : set X) (muE0 : d.-measurable E0)
  (abs : \int[mu]_(x in E0) limF x < nu E0) => proj1_sig (eps_construction muE0 abs) : {posnum R}.

Let Heps := fun (E0 : set X) (muE0 : d.-measurable E0)
  (abs : \int[mu]_(x in E0) limF x < nu E0) => proj2_sig (eps_construction muE0 abs).

Let sigma' (E0 : set X) (muE0 : d.-measurable E0)
    (abs : \int[mu]_(x in E0) limF x < nu E0) (F : set X) :=
  nu F - \int[mu]_(x in F) (limF x + (eps muE0 abs)%:num%:E)%E.

Let htmp (E0 : set X) (muE0 : d.-measurable E0)
    (abs : \int[mu]_(x in E0) limF x < nu E0) : forall U, measurable U ->
  \int[mu]_(x in U) (limF x + ((eps muE0 abs)%:num)%:E) \is a fin_num.
Proof.
move=> u mU.
rewrite ge0_integralD//; last 2 first.
  exact: measurable_funS mlimF.
  exact/EFin_measurable_fun/measurable_fun_cst.
rewrite fin_numD integral_cst// fin_numM// ?andbT; last first.
  by rewrite ge0_fin_numE// ?measure_ge0// (le_lt_trans _ mufinite) //; apply: le_measure => //; rewrite inE.
rewrite ge0_fin_numE ?measure_ge0//; last exact: integral_ge0.
rewrite (le_lt_trans _ limFoo)//.
under [in leRHS]eq_integral.
  move=> x _; rewrite gee0_abs//. over.
exact: subset_integral.
Qed.

Let sigma'_isfinite (E0 : set X) (muE0 : d.-measurable E0)
    (abs : \int[mu]_(x in E0) limF x < nu E0) :
  forall U, measurable U -> (sigma' muE0 abs) U \is a fin_num.
Proof.
move=> U mU.
rewrite /sigma' fin_numB ge0_fin_numE// ?measure_ge0 // (le_lt_trans _ nufinite)/=; last first.
  by apply: le_measure => //; rewrite inE.
exact: htmp.
Qed.

HB.instance Definition _ (E0 : set X) (muE0 : d.-measurable E0)
    (abs : \int[mu]_(x in E0) limF x < nu E0) :=
  @isSignedMeasure0.Build _ _ _ (sigma' muE0 abs) (sigma'_isfinite muE0 abs).

Let sigma'_semi_additive (E0 : set X) (muE0 : d.-measurable E0)
    (abs : \int[mu]_(x in E0) limF x < nu E0) :
  semi_additive (sigma' muE0 abs).
Proof.
move=> F' n mF' tF' mUF'.
rewrite /sigma' measure_semi_additive// big_split/= sumeN; last first.
  by move=> i _; rewrite htmp.
congr (_ - _).
rewrite ge0_integral_bigsetU//.
- rewrite -bigcup_mkord.
  have : measurable_fun setT (fun x => limF x + ((eps muE0 abs)%:num)%:E).
    by apply: emeasurable_funD => //; exact/EFin_measurable_fun/measurable_fun_cst.
  exact: measurable_funS.
- by move=> x h; rewrite adde_ge0.
- exact: sub_trivIset tF'.
Qed.

HB.instance Definition _ (E0 : set X) (muE0 : d.-measurable E0)
    (abs : \int[mu]_(x in E0) limF x < nu E0) :=
  @isAdditiveSignedMeasure.Build _ _ _ (sigma' muE0 abs) (sigma'_semi_additive muE0 abs).

Let sigma'_semi_sigma_additive (E0 : set X) (muE0 : d.-measurable E0)
   (abs : \int[mu]_(x in E0) limF x < nu E0) :
  semi_sigma_additive (sigma' muE0 abs).
Proof.
move=> F' mF' tF' mUF'.
rewrite /sigma'/=.
rewrite [X in X --> _](_ : _ = (fun n =>
  \sum_(0 <= i < n) (nu (F' i)) -
  \sum_(0 <= i < n) (\int[mu]_(x in F' i) (limF x + ((eps muE0 abs)%:num)%:E)))); last first.
  apply/funext => n.
  rewrite big_split/= sumeN// => i _.
  by rewrite htmp.
apply: __deprecated__ereal_cvgB.
    rewrite adde_defC fin_num_adde_def//.
    rewrite ge0_fin_numE// ?measure_ge0// (le_lt_trans _ nufinite)//.
    apply: le_measure => //.
      rewrite inE.
      exact: bigcup_measurable.
    by rewrite inE.
  exact: measure_semi_sigma_additive.
rewrite ge0_integral_bigcup; last 4 first.
        done.
      split.
        have : measurable_fun setT (fun x : X => limF x + ((eps muE0 abs)%:num)%:E).
          apply: emeasurable_funD => //.
          exact/EFin_measurable_fun/measurable_fun_cst.
        exact: measurable_funS.
      apply: (@le_lt_trans _ _ (\int[mu]_(x in \bigcup_k F' k) `|limF x| + \int[mu]_(x in \bigcup_k F' k)`|((eps muE0 abs)%:num)%:E|)).
        rewrite -integralD.
              apply: ge0_le_integral => //.
                  apply: measurable_fun_comp => //.
                  apply: emeasurable_funD => //.
                    by apply: measurable_funS mlimF.
                  exact/EFin_measurable_fun/measurable_fun_cst.
                apply: emeasurable_funD => //.
                  apply: measurable_fun_comp => //.
                  by apply: measurable_funS mlimF.
                apply: measurable_fun_comp => //.
                exact/EFin_measurable_fun/measurable_fun_cst.
              move=> x _.
              exact: lee_abs_add.
            done.
    (* TODO: lemma about integrability of abse *)
          split.
            apply: measurable_fun_comp => //.
            by apply: measurable_funS mlimF.
          rewrite (le_lt_trans _ limFoo)//.
          under eq_integral do rewrite abse_id.
          apply: subset_integral => //.
          by apply: measurable_fun_comp.
        split.
          apply: measurable_fun_comp => //.
          exact/EFin_measurable_fun/measurable_fun_cst.
        under eq_integral do rewrite abse_id.
        rewrite integral_cst//=.
        apply: lte_mul_pinfty => //.
        rewrite (le_lt_trans _ mufinite)//.
        by apply: le_measure => //; rewrite inE.
      apply: lte_add_pinfty.
        rewrite (le_lt_trans _ limFoo)//.
        apply: subset_integral => //.
        by apply: measurable_fun_comp => //.
      rewrite integral_cst//=.
      apply: lte_mul_pinfty => //.
      rewrite (le_lt_trans _ mufinite)//.
      by apply: le_measure => //; rewrite inE.
    move=> x _.
    by rewrite adde_ge0//.
  done.
have /cvg_ex[/= l hl] : cvg (fun x => \sum_(0 <= i < x) \int[mu]_(x0 in F' i) (limF x0 + ((eps muE0 abs)%:num)%:E)).
  apply: is_cvg_ereal_nneg_natsum => n _.
  by apply: integral_ge0 => x _; rewrite adde_ge0.
by rewrite (@cvg_lim _ _ _ _ _ _ l).
Qed.

HB.instance Definition _ (E0 : set X) (muE0 : d.-measurable E0)
    (abs : \int[mu]_(x in E0) limF x < nu E0) :=
  @isSignedMeasure.Build _ _ _ (sigma' muE0 abs) (@sigma'_semi_sigma_additive _ muE0 abs).

Lemma disj_setDI (S T : set X) : (S `\` T) `&` (S `&` T) = set0.
apply: (subsetI_eq0 (@subset_refl _ (S `\` T)) (@subIsetr _ S T)).
exact: setDKI.
Qed.

Theorem Radon_Nikodym_finite_ge0 :
  nu `<< mu -> exists f : X -> \bar R, [/\
        forall x, f x >= 0,
        integrable mu setT f &
        forall E, E \in measurable -> nu E = \int[mu]_(x in E) f x].
Proof.
(*
 * Define the measurable subsets of X to be those subsets that belong to the
 *  σ-algebra measurable on which the measures mu and nu are defined.
 *)
move => mudomnu.
(* have : forall m x, F m x >= 0
 *   forall x, 0 <= g m x, g m in G
 *)
 (* max_g2' : (T -> R)^nat :=
  fun k t => (\big[maxr/0]_(i < k) (g2' i k) t)%R. *)
exists limF; split => //.
(* Reductio ad absurdum *)
move=> E0 /[!inE] mE0.
apply/eqP; rewrite eq_le limFleqnu//.
rewrite andbT leNgt; apply/negP => abs.
pose sigma : {smeasure set X -> \bar R} := [the {smeasure set X -> \bar R} of sigma' mE0 abs].
have sigmaE : forall F, sigma F = nu F - \int[mu]_(x in F) (limF x + (eps mE0 abs)%:num%:E).
  by [].
move : (Hahn_decomposition sigma) => [P [N [[mP posP] [mN negN] PNX PN0]]].
rewrite !inE in (*mE0*) mP mN.
pose E0P := E0 `&` P.
have mE0P : measurable E0P.
  exact: measurableI.
have muE0P0: mu E0P > 0.
  rewrite lt_neqAle measure_ge0// andbT eq_sym.
  apply : (contra_not_neq (mudomnu _ mE0P)).
  apply /eqP.
  rewrite gt_eqF //.
  apply: (@lt_le_trans _ _ (sigma E0P)).
    apply: (@lt_le_trans _ _ (sigma E0)) ; last first.
      rewrite (s_measure_partition2 _ mP mN) // gee_addl //.
      apply: negN => //.
      rewrite inE.
      by apply: measurableI.
    rewrite sigmaE sube_gt0//.
    exact: Heps.
  rewrite /sigma/=/sigma' lee_subel_addl.
    apply: lee_paddl => //.
    apply: integral_ge0.
    move=> x _.
    by rewrite adde_ge0.
  rewrite (ge0_fin_numE (measure_ge0 _ _ mE0P)).
  apply : (le_lt_trans _ nufinite).
  by apply le_measure => //; rewrite inE.
pose h x := if (x \in E0P) then (limF x + ((eps mE0 abs)%:num)%:E) else (limF x).
have mh : measurable_fun setT h.
  apply: measurable_fun_if => //.
      apply: (@emeasurable_fun_bool _ _ _ _ true).
      by rewrite in_mem_mem_true.
    apply: measurable_funTS.
    apply: emeasurable_funD => //.
    exact: measurable_fun_cst.
  by apply:measurable_funTS.
have hge0 x: 0 <= h x.
  rewrite/h.
  case:ifPn => // _.
  by rewrite adde_ge0.
have hnuP : forall S, measurable S -> S `<=` E0P -> \int[mu]_(x in S) h x <= nu S.
  move=> S mS SE0P.
  have : sigma S >= 0.
    apply: posP.
      by rewrite inE.
    apply: (subset_trans SE0P).
    by apply: subIsetr.
  rewrite sigmaE.
  rewrite sube_ge0; last first.
  apply /orP; right.
    rewrite ge0_fin_numE // ?measure_ge0//.
    apply: (le_lt_trans _ nufinite).
    by apply le_measure => //; rewrite inE.
  apply: le_trans.
  rewrite -{1}(setIid S) integral_mkcondr le_eqVlt ; apply/orP; left.
  apply /eqP.
  apply eq_integral.
  move=> x Sx.
  rewrite /restrict /h !ifT // inE.
  apply : SE0P.
  by rewrite inE in Sx.
have hnuN : forall S, measurable S -> S `<=` ~` E0P -> \int[mu]_(x in S) h x <= nu S.
  move=> S mS ScE0P.
  rewrite /h.
  under eq_integral.
    move=> x xS.
    rewrite ifF; last first.
      apply /negbTE.
      rewrite notin_set.
      apply ScE0P.
      by rewrite inE in xS.
    over.
  exact: limFleqnu.
have hnu : forall S, measurable S -> \int[mu]_(x in S) h x <= nu S.
  move=> S mS.
  rewrite -(setD0 S) -(setDv E0P) setDDr.
  have mSIE0P : measurable (S `&` E0P).
    by apply measurableI.
  have mSDE0P : measurable (S `\` E0P).
    by apply measurableD.
  rewrite integral_setU //; last 2 first.
      by apply:(measurable_funS measurableT).
    rewrite disj_set2E.
    apply /eqP.
    exact: disj_setDI.
  rewrite measureU //.
  apply: lee_add.
      by apply: hnuN.
    by apply: hnuP.
  exact: disj_setDI.
(* have posE0P : positive_set sigma E0P. *)
have inthgtM : \int[mu]_(x in setT) h x > M.
  have mCE0P := (measurableC mE0P).
  have disj_UvE0P :[disjoint E0P & ~`E0P].
    apply/disj_set2P.
    exact:setICr.
  rewrite -(setUv E0P) integral_setU //; last first.
    by rewrite setUv.
  rewrite /h -(eq_integral _ (fun x => limF x + ((eps mE0 abs)%:num)%:E)); last first.
    move=> x xE0P.
    by rewrite ifT.
  rewrite -[\int[mu]_(x in ~`E0P) _](eq_integral _ (fun x => limF x)); last first.
    move=> x.
    rewrite inE /= => xnp.
    by rewrite memNset.
  rewrite ge0_integralD//; last 2 first.
      by apply: measurable_funTS.
    exact : measurable_fun_cst.
  rewrite integral_cst // addeAC -integral_setU //; last first.
      by rewrite setUv.
  rewrite setUv limFXeqM -lte_subel_addl; last first.
    by rewrite ge0_fin_numE// ?sup_RN_approx_integral_lty// sup_RN_approx_integral_ge0.
  rewrite subee //.
    by apply: mule_gt0.
  by rewrite sup_RN_approx_integral_fin_num.
have hinG: G h.
  rewrite /G //=.
  split => //=; last first.
    move=> S.
    rewrite inE.
    by apply: hnu.
  split => //.
  under eq_integral do rewrite gee0_abs //.
  by apply: (le_lt_trans (hnu setT measurableT)).
have : (\int[mu]_x h x <= M).
  rewrite -(ereal_sup1 (\int[mu]_x h x)).
  apply (@le_ereal_sup _ [set \int[mu]_x h x] IG).
  rewrite sub1set inE.
  exists h => //.
rewrite leNgt.
by rewrite inthgtM.
Qed.

End Radon_Nikodym_finite_ge0.

Theorem Radon_Nikodym_sigma_finite_ge0 d (X : measurableType d) (R : realType)
    (mu : {measure set X -> \bar R}) (nu : {measure set X -> \bar R})
    (nufinite : (nu setT < +oo)%E)
    (sigma_finite_mu : sigma_finite setT mu) :
  nu `<< mu -> exists f : X -> \bar R,
  integrable mu setT f /\ forall E, E \in measurable -> nu E = integral mu E f.
Proof.
(* assume that nu is non-negative *)
move: sigma_finite_mu => [F TF mFAFfin].
have [mF Ffin] := all_and2 mFAFfin.
move: mFAFfin => _.
pose E := seqDU F.
have mE : forall j, measurable (E j).
  (* bigsetU_measurable. *)
  move=> j.
  apply: measurableD => //.
  by apply: bigsetU_measurable => //.
have disj_E := (@trivIset_seqDU _ F).
have Efin : forall j, mu (E j) < +oo.
  move=> j.
  have mE_j' : (E j) \in measurable.
    by rewrite inE.
  apply:(@le_lt_trans _ _ (mu (F j))).
    apply:(le_measure _ mE_j').
      by rewrite inE.
    exact: subDsetl.
  by apply: Ffin.
have TE : \bigcup_i E i = setT.
  rewrite TF.
  by rewrite [RHS]seqDU_bigcup_eq.
pose mu_ j := mrestr mu (mE j): {measure set X -> \bar R}.
pose nu_ j := mrestr nu (mE j): {measure set X -> \bar R}.
have mu_finite : forall n, mu_ n setT < +oo.
  move=> j.
  by rewrite /mu_ /= /mrestr setTI.
have nu_finite : forall n, nu_ n setT < +oo.
  move=> j.
  rewrite /nu_ /= /mrestr setTI.
  apply: (@le_lt_trans _ _ (nu setT)) => //.
  by apply:le_measure => //; rewrite inE.
move=> nudommu.
have nu_dommu_ j : nu_ j `<< mu_ j.
  move=> S mS mu_jS0.
  apply: nudommu => //.
  by apply: measurableI.
have [f_tilde Hf_tilde] := choice (fun j =>
            Radon_Nikodym_finite_ge0 (mu_finite j) (nu_finite j) (nu_dommu_ j)).
have [f_tilde_ge0 int_f_tildeT int_f_tildeE] := all_and3 Hf_tilde.
move: Hf_tilde => _.
pose f_ j x := if (x \in E j) then f_tilde j x else 0.
have f_ge0 : forall j x, 0 <= f_ j x.
  move=> j x.
  rewrite /f_.
  by case: ifP.
have mf_ : forall j, measurable_fun setT (f_ j).
  move=> j.
  rewrite /f_.
  apply: measurable_fun_if => //.
      apply: (@emeasurable_fun_bool _ _ _ _ true).
      by rewrite in_mem_mem_true.
    rewrite in_mem_mem_true.
    apply: (measurable_funS measurableT) => //.
    by apply (int_f_tildeT j).
  rewrite in_mem_mem_false.
  apply: (measurable_funS measurableT) => //.
  exact: measurable_fun_cst.
have int_f_T : forall j, integrable mu setT (f_ j).
  move=> j.
  split => //.
  under eq_integral.
    move=> x _.
    rewrite gee0_abs; last first.
    exact: f_ge0.
    over.
  rewrite -(setUv (E j)).
  rewrite integral_setU //; last 3 first.
        by apply: measurableC.
      by rewrite setUv.
    apply/disj_set2P.
    apply subsets_disjoint => //.
  rewrite /f_ -(eq_integral _ (fun x => f_tilde j x)); last first.
    move=> x Ejx.
    by rewrite ifT.
  rewrite (@eq_measure_integral _ _ _ (E j) (mu_ j)); last first.
    move=> A mA AEj.
    by rewrite /mu_ /= /mrestr setIidl.
  rewrite -int_f_tildeE ?inE //.
  under eq_integral.
    move=>x.
    rewrite inE /= => nEjx.
    rewrite ifF; last first.
      by rewrite memNset.
    over.
  rewrite integral0 adde0.
  rewrite /nu_ /= /mrestr setIid.
  apply: (@le_lt_trans _ _ (nu setT)) => //.
  by apply:le_measure; rewrite ?inE.
have int_f_E: forall j S, measurable S -> \int[mu]_(x in S) f_ j x = nu (S `&` E j).
  move=> j S mS.
  have mSIEj := measurableI _ _ mS (mE j).
  have mSDEj := measurableD mS (mE j).
  rewrite -{1}(setUIDK S (E j)).
  rewrite (integral_setU _ mSIEj mSDEj); last 3 first.
        rewrite setUIDK.
        by apply: (measurable_funS measurableT).
      move=> x.
      rewrite setUIDK => Sx.
      rewrite /f_.
      by case: ifP.
    apply/disj_set2P.
    rewrite setIC.
    exact: disj_setDI.
  rewrite /f_ -(eq_integral _ (fun x => f_tilde j x)); last first.
    move=> x.
    rewrite inE => SIEjx.
    rewrite /f_ ifT //.
    rewrite inE.
    by apply: (@subIsetr _ S (E j)).
  rewrite (@eq_measure_integral _ _ _ (S `&` E j) (mu_ j)); last first.
    move=> A mA.
    rewrite subsetI; move => [_ Ejx].
    by rewrite /mu_ /= /mrestr setIidl.
  rewrite -int_f_tildeE; last first.
    rewrite inE.
    by apply measurableI.
  under eq_integral.
    move=> x.
    rewrite inE setDE /=; move=> [_ nEj].
    rewrite ifF; last first.
      by rewrite memNset.
    over.
  rewrite integral0 adde0.
  by rewrite /nu_ /= /mrestr -setIA setIid.
(*
pose f x : \bar R := \esum_(i in [set _ | true]) f_ i x. *)
(* this definition will need less nneseries_esum and proving forall n : nat, true -> 0 <= _
   than use \sum_(j<oo) to define. But we can't do rewrite -nneseries then proved following:
*)
have esum_sum_ge0 :forall (P: nat -> \bar R),(forall n, 0 <= P n) -> \esum_(i in [set _ | true]) P i = \sum_(i <oo) P i.
  move=>P P0.
  by rewrite nneseries_esum.

pose f x : \bar R := \sum_(j <oo) (f_ j x).
exists f.
have mf : measurable_fun setT f.
  by apply: ge0_emeasurable_fun_sum.
have fge0 : forall x, 0 <= f x.
  move=> x.
  rewrite /f nneseries_esum; last by move=> n _; apply: f_ge0.
  by apply: esum_ge0.
have intfgenu : \int[mu]_x f x = nu setT.
(*  apply/eqP; rewrite eq_le; apply/andP; split. *)
  rewrite integral_nneseries //.
  rewrite nneseries_esum; last first.
    move=> m _.
    by rewrite integral_ge0.
  under eq_esum => /=.
    move=> n _.
    rewrite int_f_E //.
    rewrite setTI.
    over.
  move=> //.
  rewrite esum_sum_ge0 //; last first.
    by move=> n; rewrite measure_ge0.
  rewrite -measure_bigcup //.
  by rewrite TE.
split.
  split => //.
  under eq_integral => x _.
    rewrite gee0_abs; last first.
      by apply: nneseries_ge0.
    over.
  by rewrite intfgenu.
move=> E0; rewrite inE => mE0.
rewrite integral_nneseries//; last first.
  move=> n.
  by apply: (measurable_funS measurableT).
rewrite nneseries_esum; last first.
  move=> m _.
  by rewrite integral_ge0.
under eq_esum => /=.
  move=> n _.
  rewrite int_f_E //.
  over.
move=> //.
rewrite esum_sum_ge0 //; last first.
  move=> n; rewrite measure_ge0 //.
  by apply: measurableI.
rewrite -measure_bigcup //;last 2 first.
    move=> i.
    by apply: measurableI => //.
  apply: trivIset_setI.
  exact: disj_E.
by rewrite -setI_bigcupr TE setIT.
Qed.

(* TODO: move? *)
Lemma fin_num_sume_distrr (R : realType) (I : Type) (s : seq I) r (P : pred I)
    (F : I -> \bar R) : (forall i, P i -> F i \is a fin_num) ->
  r%:E * (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) (r%:E * F i).
Proof.
move=> PF; elim/big_rec2 : _ => //; first by rewrite mule0.
by move=> i y1 y2 Pi <-; rewrite muleDr// adde_defC fin_num_adde_def// PF.
Qed.

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

(* unused *)
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

Section measure_of_smeasure.
Variables (d : _) (X : measurableType d) (R : realType).
Variable (mu : {smeasure set X -> \bar R}).
Variable (mu_is_non_negative : positive_set mu setT).

Definition measure_of_smeasure := (fun (_ : positive_set mu setT) (S : set X) =>
                                     mu S).
Local Notation measure_mu := (measure_of_smeasure mu_is_non_negative).

Let mu0 : measure_mu set0 = 0.
Proof. exact: smeasure0. Qed.

Let mu_ge0 : forall S, measurable S ->  0 <= measure_mu S.
Proof.
move=> E mE.
move: mu_is_non_negative.
move=> [] _ -> //.
by rewrite inE.
Qed.

Let mu_sigma_additive : semi_sigma_additive measure_mu.
Proof. exact: smeasure_semi_sigma_additive. Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  (measure_of_smeasure mu_is_non_negative)
  mu0 mu_ge0 mu_sigma_additive.

Lemma measure_of_smeasureE S : measure_mu S = mu S.
Proof. by []. Qed.

End measure_of_smeasure.

Arguments measure_of_smeasure {d X R}.

Section Jordan_measure_decomposition.
Variables (d : _) (X : measurableType d) (R : realType).
Variables (nu: {smeasure set X -> \bar R}).

(* P N mP mNを Hahn_decomposition nuから取り出して一度に全てまとめて定義したい *)
(*
Definition [P [N [[mP posP] [mN negN] PN0 PNT] := Hahn_decomposition nu.
*)

Variables (P N: set X).
Hypothesis nuPN : is_Hahn_decomposition nu P N.

Let mP : measurable P.
by have [[mP _] _ _ _] := nuPN ; rewrite inE in mP.
Qed.

Let mN : measurable N.
by have [_ [mN _] _ _] := nuPN; rewrite inE in mN.
Qed.

Definition nu_p' : {smeasure set X -> \bar R} := smrestr nu mP.

Definition positive_nu_p' : positive_set nu_p' setT.
have [posP _ _ _] := nuPN.
split;[|move=> E]; rewrite inE // => mE _.
rewrite /nu_p'/smrestr/=/smrestr.
by apply posP; rewrite ?inE; [apply measurableI|apply subIsetr].
Qed.

Definition nu_n' : {smeasure set X -> \bar R} := smscale (-1) (smrestr nu mN).

Definition positive_nu_n' : positive_set nu_n' setT.
Proof.
split; first by rewrite inE.
move=> E /[1!inE]mE _; rewrite /nu_n' /= /smscale /= /smrestr muleC mule_le0//.
by move: nuPN => [_ [_ +] _ _] => ->//; rewrite inE; exact: measurableI.
Qed.

Definition nu_p : {measure set X -> \bar R} := measure_of_smeasure _ positive_nu_p'.
Definition nu_n : {measure set X -> \bar R} := measure_of_smeasure _ positive_nu_n'.

Lemma nu_pfinite : nu_p setT < +oo.
Proof.
by rewrite /nu_p/= /smrestr setTI fin_num_ltey// isfinite.
Qed.

Lemma nu_nfinite : nu_n setT < +oo.
Proof.
rewrite /nu_n/= /smscale/= EFinN mulN1e /smrestr setTI fin_num_ltey//.
by rewrite fin_numN isfinite.
Qed.

Lemma nu_pfinite : nu_p setT < +oo.
Proof.
by rewrite /nu_p/= /smrestr setTI fin_num_ltey// isfinite.
Qed.

Lemma nu_nfinite : nu_n setT < +oo.
Proof.
rewrite /nu_n/= /smscale/= EFinN mulN1e /smrestr setTI fin_num_ltey//.
by rewrite fin_numN isfinite.
Qed.

(* Jordan_measure_decomposition のargumentsがnuだけになるようにしたい*)

Definition Jordan_measure_decomposition := (nu_p, nu_n).

(* Lemma nu_dcmp : nu = smeasure_add nu'_p nu'_n. *)

Lemma nu_dcmp A : measurable A -> nu A = nu_p A - nu_n A.
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


End Jordan_measure_decomposition.

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

Section smeasure_add.
Local Open Scope ereal_scope.
Variables (d : measure_display) (T : measurableType d) (R : realType).
Variables (m1 m2 : {smeasure set T -> \bar R}).

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
move=> nudommu.
have [P [N HahnPN]] := Hahn_decomposition nu.
have [posP negN PNX PN0] := HahnPN.
have [mN _] := negN.
rewrite inE in mN.
(* Jordan decomposition *)
pose nu_p := nu_p HahnPN.
pose nu_n := nu_n HahnPN.
(* nu_p an_d nu_n are finite measures *)
have nu_pfinite : nu_p setT < +oo by exact: nu_pfinite.
have nu_nfinite : nu_n setT < +oo by exact: nu_nfinite.
have nu_pdommu : nu_p `<< mu.
  move=> A mA muA0.
  have := nudommu A mA muA0.
  rewrite (nu_dcmp HahnPN)//=.
  rewrite /smrestr/= /smscale/= /smrestr/= EFinN mulN1e oppeK.
  have mAP : measurable (A `&` P).
    apply: measurableI => //.
    by case: posP; rewrite inE.
  have muAP0 : mu (A `&` P) = 0.
    apply/eqP; rewrite eq_le; apply/andP; split.
      rewrite -muA0.
      apply: le_measure => //.
      by rewrite inE.
      by rewrite inE.
    by rewrite measure_ge0.
  by have -> := nudommu _ mAP muAP0.
have nu_ndommu : nu_n `<< mu.
  move=> A mA muA0.
  have := nudommu A mA muA0.
  rewrite (nu_dcmp HahnPN)//=.
  rewrite /smrestr/= /smscale/= /smrestr/= EFinN mulN1e oppeK.
  have mAN : measurable (A `&` N).
    by apply: measurableI => //.
  have muAN0 : mu (A `&` N) = 0.
    apply/eqP; rewrite eq_le; apply/andP; split.
      rewrite -muA0.
      apply: le_measure => //.
      by rewrite inE.
      by rewrite inE.
    by rewrite measure_ge0.
  have -> := nudommu _ mAN muAN0.
  by rewrite oppe0.
(* f_p := Radon_Nikodym_sigma_finite_ge0 nu_pdommu*)
have [f_p [intf_p f_pE]] := Radon_Nikodym_sigma_finite_ge0 nu_pfinite sigma_finite_mu nu_pdommu.
have [f_n [intf_n f_nE]] := Radon_Nikodym_sigma_finite_ge0 nu_nfinite sigma_finite_mu nu_ndommu.
pose f := f_p \- f_n.
exists f.
split.
  apply: integrableB => //.
move=> E.
rewrite inE => mE.
rewrite [LHS](nu_dcmp HahnPN mE)// integralB; last 3 first.
      exact: mE.
    by apply: (integrableS measurableT).
  by apply: (integrableS measurableT).
rewrite -f_pE//; last by rewrite inE.
by rewrite -f_nE//; last by rewrite inE.
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
