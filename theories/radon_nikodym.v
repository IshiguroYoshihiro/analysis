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
      move/cvgPpinfty : lims => /(_ e%:num^-1) [N _] /(_ _ (leqnn N)).
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
  move/cvgPpinfty_lt : limk => /(_ (s_ (v n))%:R) [m _ Hm].
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
- by move=> E _; by rewrite integral0.
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
  by rewrite ge0_fin_numE//.
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
by rewrite integral0.
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
by apply: ereal_lim_ge => //; exact: nearW.
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
rewrite int_limFE// ereal_lim_le//; first exact: is_cvg_int_F.
by apply: nearW => n; have [_ /andP[_ ]] := H3 n.
Qed.

Let limFleqnu E0 : measurable E0 -> \int[mu]_(x in E0) limF x <= nu E0.
Proof.
move=> mE0; rewrite int_limFE// ereal_lim_le //; first exact: is_cvg_int_F.
by apply: nearW => n; exact: Fleqnu.
Qed.

Let limFXeqM : \int[mu]_x limF x = M.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite int_limFE// ereal_lim_le //; first exact: is_cvg_int_F.
  by apply: nearW => n; have [_ /andP[_]] := H3 n.
rewrite int_limFE//.
have Htmp : (fun m => M - (m.+1%:R^-1)%:E) --> M.
  rewrite -[X in _ --> X]sube0.
  apply: ereal_cvgB.
  + by rewrite fin_num_adde_def.
  + exact: cvg_cst.
  + apply/ereal_cvg_real; split; first by apply: nearW.
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
rewrite neq_lt ltNge measure_ge0/= => muE0_gt0.
pose mid := ((fine (nu E0) - fine (\int[mu]_(x in E0) limF x)) / 2)%R.
pose e := (mid / fine (mu E0))%R.
have ? : \int[mu]_(x in E0) limF x \is a fin_num.
  rewrite ge0_fin_numE// ?isfinite// ?(lt_le_trans abs)// ?leey//.
  exact: integral_ge0.
have ? : nu E0 \is a fin_num.
  rewrite ge0_fin_numE// (le_lt_trans _ nufinite)//.
  by apply: le_measure => //; rewrite ?inE.
have e_gt0 : (0 < e)%R.
  rewrite /e divr_gt0//; last by rewrite fine_gt0// muE0oo// andbT.
  by rewrite divr_gt0// subr_gt0// fine_lt.
exists (PosNum e_gt0); rewrite ge0_integralD//; last 2 first.
  exact: measurable_funS mlimF.
  exact: measurable_fun_cst.
rewrite integral_cst// -lte_subr_addr//; last first.
  by rewrite fin_numM// ?ge0_fin_numE// muE0oo.
rewrite -{2}(@fineK _ (mu E0)); last by rewrite ge0_fin_numE// muE0oo.
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
  by rewrite ge0_fin_numE// (le_lt_trans _ mufinite)//; apply: le_measure => //; rewrite inE.
rewrite ge0_fin_numE; last exact: integral_ge0.
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
rewrite /sigma' fin_numB ge0_fin_numE// (le_lt_trans _ nufinite)/=; last first.
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
apply: ereal_cvgB.
  rewrite adde_defC fin_num_adde_def//.
  rewrite ge0_fin_numE// (le_lt_trans _ nufinite)//.
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
    apply: measurable_fun_comp => //.
    split.
      apply: measurable_fun_comp => //.
      exact/EFin_measurable_fun/measurable_fun_cst.
    under eq_integral do rewrite abse_id.
    rewrite integral_cst//=.
    apply: lte_mul_pinfty => //.
      rewrite lee_fin//.
     by rewrite normr_ge0.
    rewrite (le_lt_trans _ mufinite)//.
    by apply: le_measure => //; rewrite inE.
  apply: lte_add_pinfty.
    rewrite (le_lt_trans _ limFoo)//.
    apply: subset_integral => //.
    by apply: measurable_fun_comp => //.
  rewrite integral_cst//=.
  apply: lte_mul_pinfty => //.
    rewrite lee_fin//.
    by rewrite normr_ge0.
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
  rewrite lt_neqAle measure_ge0 andbT eq_sym.
  apply : (contra_not_neq (mudomnu _ mE0P)).
  apply /eqP.
  rewrite gt_eqF //.
  apply: (@lt_le_trans _ _ (sigma E0P)).
    apply: (@lt_le_trans _ _ (sigma E0)) ; last first.
      rewrite (s_measure_partition2 _ _ _ PNX) // gee_addl //.
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
  rewrite (ge0_fin_numE (measure_ge0 nu E0P)).
  apply : (le_lt_trans _ nufinite).
  by apply le_measure => //; rewrite inE.
pose h x := if (x \in E0P) then (limF x + ((eps mE0 abs)%:num)%:E) else (limF x).
have mh : measurable_fun setT h.
  apply: measurable_fun_if => //.
      apply: (@emeasurable_fun_bool _ _ _ _ true).
      by rewrite in_mem_mem_true.
    rewrite in_mem_mem_true setTI.
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
  apply /orP.
  right.
    rewrite ge0_fin_numE //.
    apply: (le_lt_trans _ nufinite).
    by apply le_measure => //; rewrite inE.
  apply: le_trans.
  rewrite -{1}(setIid S).
  rewrite integral_mkcondr.
  rewrite le_eqVlt ; apply/orP; left.
  apply /eqP.
  apply eq_integral.
  move=> x xS.
  rewrite /restrict /h.
  rewrite xS.
  rewrite ifT //.
  rewrite inE.
  apply : SE0P.
  by rewrite inE in xS.
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
  pose E0PS := E0P `&` S.
  have mE0PS : measurable E0PS.
   by apply measurableI.
  have Sdcm : S = E0PS `|` (S `\` E0PS).
    rewrite setDUK //.
    exact: subIsetr.
  rewrite Sdcm.
  rewrite integral_setU //; last 3 first.
        by apply measurableD.
      apply measurable_funU => //.
        by apply measurableD.
        split.
          apply: measurable_fun_if => //.
            apply: (@emeasurable_fun_bool _ _ _ _ true) => //.
            by rewrite in_mem_mem_true.
          rewrite in_mem_mem_true.
          rewrite setIidl; last first.
            exact: subIsetl.
          apply: emeasurable_funD.
            by apply: (measurable_funS measurableT).
          exact: measurable_fun_cst.
        by apply: (measurable_funS measurableT).
      apply: measurable_fun_if.
            by apply:measurableD.
          apply: (@emeasurable_fun_bool _ _ _ _ true) => //.
          by rewrite in_mem_mem_true.
        apply: emeasurable_funD => //.
          by apply:(measurable_funS measurableT).
        by apply:measurable_fun_cst.
      by apply:(measurable_funS measurableT).
    rewrite disj_set2E.
    apply /eqP.
    exact: setDIK.
  rewrite measureU //; last 2 first.
      by apply measurableD.
    exact: setDIK.
  apply: lee_add.
    apply: hnuP => //.
    by apply: subIsetl.
  apply: hnuN.
    by apply: measurableD.
  rewrite -setTD.
  rewrite setDIr.
  rewrite setDv setU0.
  by apply: setSD.
(* have posE0P : positive_set sigma E0P. *)
have inthgtM : \int[mu]_(x in setT) h x > M.
  rewrite -(setUv E0P).
  rewrite integral_setU //; last 3 first.
        by apply measurableC.
      rewrite measurable_funU //; last first.
        by apply measurableC.
      split.
        apply (@measurable_restrict _ _ _ _ E0P setT h) => //.
        have he0p : h \_ E0P =
                      (fun x => limF x + ((eps mE0 abs)%:num)%:E) \_ E0P.
          apply eq_restrictP.
          move=> x xe0p.
          rewrite /h ifT //.
        rewrite he0p.
        apply measurable_restrict => //.
        apply measurable_funTS.
        apply emeasurable_funD => //.
        by apply measurable_fun_cst.
      apply (@measurable_restrict _ _ _ _ (~`E0P) setT h) => //.
        by apply measurableC.
      have hce0p : h \_ (~`E0P) = (fun x => limF x) \_ (~`E0P).
        apply eq_restrictP.
        move=> x.
        rewrite inE /=.
        rewrite /h => xne0p.
        by rewrite memNset.
      rewrite hce0p.
      apply measurable_restrict => //.
        by apply measurableC.
      by apply measurable_funTS.
    apply /disj_set2P.
    exact : setICr.
  rewrite /h.
  rewrite -(eq_integral _ (fun x => limF x + ((eps mE0 abs)%:num)%:E)); last first.
    move=> x xE0P.
    by rewrite ifT.
  rewrite -[\int[mu]_(x in ~`E0P) _](eq_integral _ (fun x => limF x)); last first.
    move=> x.
    rewrite inE /= => xnp.
    rewrite memNset //.
  rewrite ge0_integralD//; last 2 first.
      by apply: measurable_funTS.
    exact : measurable_fun_cst.
  rewrite integral_cst //.
  rewrite addeAC.
  rewrite -integral_setU //; last 3 first.
        by apply measurableC.
      by rewrite setUv.
    apply /disj_set2P.
    exact : setICr.
  rewrite setUv.
  rewrite limFXeqM.
  rewrite -lte_subel_addl; last first.
    by rewrite ge0_fin_numE// ?sup_RN_approx_integral_lty// sup_RN_approx_integral_ge0.
  rewrite subee //.
    by apply: mule_gt0.
  by rewrite sup_RN_approx_integral_fin_num.
have hinG: G h.
  rewrite /G //=.
  split => //=.
    split.
      exact: mh.
    under eq_integral => x Tx.
      rewrite gee0_abs //.
      over.
    apply: (le_lt_trans (hnu setT measurableT)) => //.
  move=> S.
  rewrite inE.
  apply : hnu.
have : (\int[mu]_x h x <= M).
  rewrite -(ereal_sup1 (\int[mu]_x h x)).
  apply (@le_ereal_sup _ [set \int[mu]_x h x] IG).
  rewrite sub1set inE.
  exists h => //.
rewrite leNgt.
by rewrite inthgtM.
Qed.

End Radon_Nikodym_finite_ge0.

Theorem Radon_Nikodym d (X : measurableType d) (R : realType)
    (mu : {measure set X -> \bar R}) (nu : {smeasure set X -> \bar R})
    (sigma_finite_mu : sigma_finite setT mu) :
  nu `<< mu -> exists f : X -> \bar R,
  integrable mu setT f /\ forall E, E \in measurable -> nu E = integral mu E f.
Proof.
Abort.

Theorem FTC2 (R : realType) (f : R -> R) (a b : R)
     (f_abscont : abs_continuous_function f (a, b) )
       : exists f' : R -> \bar R, summable `[a, b] f' /\
         {ae lebesgue_measure, forall x, x \in `[a, b] ->f' x \is a fin_num}
           /\ forall x, x \in `[a, b] ->
             (f x - f a)%:E = (integral lebesgue_measure `[a ,x] f').
Proof.
Abort.
