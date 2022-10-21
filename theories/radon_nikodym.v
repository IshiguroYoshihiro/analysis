(* -*- company-coq-local-symbols: (("`&`" . ?∩) ("`|`" . ?∪) ("set0" . ?∅)); -*- *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
Require Import boolp reals ereal classical_sets signed topology numfun.
Require Import mathcomp_extra functions normedtype.
From HB Require Import structures.
Require Import sequences esum measure fsbigop cardinality set_interval.
Require Import realfun.
Require Import lebesgue_measure lebesgue_integral.

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

(* NB: to appear in the next release of Coq *)
Section dependent_choice_Type.
Variables (X : Type) (R : X -> X -> Prop).

Lemma dependent_choice_Type : (forall x : X, {y | R x y}) ->
  forall x0, {f : nat -> X | f O = x0 /\ forall n, R (f n) (f n.+1)}.
Proof.
move=> h x0.
set (f := fix f n := if n is n'.+1 then proj1_sig (h (f n')) else x0).
exists f; split => //.
intro n; induction n; simpl; apply proj2_sig.
Qed.
End dependent_choice_Type.

(* maybe rewrite I : R * R to I : interval R *)
Definition abs_continuous_function (R : realType) (f : R -> R) (I : R * R)
    := forall e : {posnum R}, exists d : {posnum R},
         forall J : nat -> R * R, forall n : nat,
           \sum_(k < n)((J k).2 - (J k).1) < d%:num ->
             trivIset setT (fun n => `[(J n).1, (J n).2]%classic) ->
               (forall n, I.1 <= (J n).1 /\ (J n).2 <= I.2 ) ->
                 \sum_(k < n) `| f (J k).2 - f (J k).1 | < e%:num.

Local Open Scope ereal_scope.

(* this is a PR in progress *)
Lemma fine_le (R : numDomainType) : {in fin_num &, {homo @fine R : x y / x <= y >-> (x <= y)%R}}.
Proof. by move=> [? [?| |]| |]. Qed.

(* this is a PR in progress *)
Lemma sum_fine (R : numDomainType) (I : Type) s (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> F i \is a fin_num) ->
  (\sum_(i <- s | P i) fine (F i) = fine (\sum_(i <- s | P i) F i))%R.
Proof.
move=> h; apply: EFin_inj; rewrite -sumEFin fineK.
  by apply eq_bigr => ? ?; rewrite fineK// h.
rewrite sum_fin_num; apply/allP => x; elim: s => //= a b ih.
by case: ifPn => // /h ? /[!inE] /predU1P[->//|]; exact: ih.
Qed.

(* this is a PR in progress *)
Lemma sub1set (T : Type) (x : T) A : ([set x] `<=` A) = (x \in A).
Proof. by apply/propext; split=> [|/[!inE] xA _ ->//]; rewrite inE; exact. Qed.

Lemma lteN10 (R : numDomainType) : (- (1) < 0 :> \bar R)%E.
Proof. by rewrite lte_fin ltrN10. Qed.

Lemma le0_fin_numE {R : realDomainType} [x : \bar R] : x <= 0 -> (x \is a fin_num) = (-oo < x).
Proof. by move: x => [x| |]//=; rewrite lee_fin => x0; rewrite ltNye. Qed.

Lemma fine_lt0 {R : numDomainType} [x : \bar R] : -oo < x < 0 -> (fine x < 0)%R.
Proof. by move: x => [x| |] //= /andP[_]; rewrite lte_fin. Qed.

Lemma fine_le0 {R : numDomainType} [x : \bar R] : x <= 0 -> (fine x <= 0)%R.
Proof. by case: x. Qed.

Lemma lee_sum_npos_ord (R : realDomainType) (f : nat -> \bar R) (P : pred nat) :
  (forall n, P n -> f n <= 0) ->
  {homo (fun n => \sum_(i < n | P i) f i) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 i j le_ij.
rewrite [in leRHS](big_ord_widen_cond j) // big_mkcondr /=.
by rewrite lee_sum// => k ?; case: ifP => // _; exact: f0.
Qed.

Lemma lee_sum_npos_natr (R : realDomainType) (f : nat -> \bar R) (P : pred nat) m :
  (forall n, (m <= n)%N -> P n -> f n <= 0) ->
  {homo (fun n => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 i j le_ij; rewrite -[m]add0n !big_addn !big_mkord.
apply: (@lee_sum_npos_ord _ (fun k => f (k + m)%N) (fun k => P (k + m)%N));
  by [move=> n /f0; apply; rewrite leq_addl | rewrite leq_sub2r].
Qed.

Lemma is_cvg_ereal_npos_natsum_cond (R : realType) m (u_ : (\bar R)^nat)
  (P : pred nat) : (forall n, (m <= n)%N -> P n -> u_ n <= 0) ->
  cvg (fun n => \sum_(m <= i < n | P i) u_ i).
Proof.
move/lee_sum_npos_natr/ereal_nonincreasing_cvg => cu; apply: cvgP; exact: cu.
Qed.

Lemma lee_npeseries (R : realType) (u v : (\bar R)^nat) (P : pred nat) :
  (forall i, P i -> u i <= 0) -> (forall n, P n -> v n <= u n) ->
  \sum_(i <oo | P i) v i <= \sum_(i <oo | P i) u i.
Proof.
move=> u0 Puv; apply: lee_lim.
- by apply: is_cvg_ereal_npos_natsum_cond => n _ /[dup] Pn /Puv/le_trans; apply; apply/u0.
- by apply: is_cvg_ereal_npos_natsum_cond => n _ Pn; exact/u0.
- by near=> n; exact: lee_sum.
Unshelve. all: by end_near. Qed.

Lemma is_cvg_npeseries_cond (R : realType) (u_ : (\bar R)^nat)
  (P : pred nat) : (forall n, P n -> u_ n <= 0) ->
  cvg (fun n => \sum_(0 <= i < n | P i) u_ i).
Proof. by move=> u_le0; apply: is_cvg_ereal_npos_natsum_cond => n _ /u_le0. Qed.

Lemma is_cvg_npeseries (R : realType) (u_ : (\bar R)^nat)
  (P : pred nat) : (forall n, P n -> u_ n <= 0) ->
  cvg (fun n => \sum_(0 <= i < n | P i) u_ i).
Proof. by move=> ?; exact: is_cvg_npeseries_cond. Qed.

Lemma npeseries_le0 [R : realType] [u_ : (\bar R) ^nat] [P : pred nat] :
  (forall n : nat, P n -> u_ n <= 0) -> \sum_(i <oo | P i) u_ i <= 0.
Proof.
move=> u0; apply: (ereal_lim_le (is_cvg_npeseries u0)).
by near=> k; rewrite sume_le0 // => i; apply: u0.
Unshelve. all: by end_near. Qed.

(* NB: PR in progress *)
Lemma inv_cvg (R : realType) (u : R ^nat) :
  (forall n, 0 < u n)%R ->
  (fun n => (u n)^-1) --> (0 : R)%R -> u --> +oo%R.
Proof.
move=> u0 uV0; apply/cvgPpinfty => M.
move/(@cvg_distP _ [normedModType R of R^o]) : uV0 => /(_ (`|M| + 1)^-1%R).
rewrite invr_gt0 ltr_paddl// => /(_ erefl); rewrite !near_map.
apply: filterS => n.
rewrite sub0r normrN normrV ?unitfE ?gt_eqF//.
rewrite ger0_norm; last by rewrite ltW.
rewrite ltr_pinv; last 2 first.
  by rewrite inE unitfE u0 andbT gt_eqF.
  by rewrite inE unitfE ltr_paddl// andbT gt_eqF.
move/ltW; apply: le_trans.
by rewrite (le_trans (ler_norm _))// ler_addl.
Qed.

(* NB: PR in progress *)
Lemma nneseries_is_cvg (R : realType) (u : nat -> R) :
  (forall i, 0 <= u i)%R -> \sum_(k <oo) (u k)%:E < +oo -> cvg (series u).
Proof.
move=> ? ?; apply: nondecreasing_is_cvg.
  move=> m n mn; rewrite /series/=.
  rewrite -(subnKC mn) {2}/index_iota subn0 iotaD big_cat/=.
  by rewrite add0n -{2}(subn0 m) -/(index_iota _ _) ler_addl sumr_ge0.
exists (fine (\sum_(k <oo) (u k)%:E)).
rewrite /ubound/= => _ [n _ <-]; rewrite -lee_fin fineK//; last first.
  rewrite fin_num_abs gee0_abs//; apply: nneseries_ge0 => // i _.
  by rewrite lee_fin.
by rewrite -sumEFin; apply: nneseries_lim_ge => i _; rewrite lee_fin.
Qed.

(* NB: PR in progress *)
Lemma bigsetU_sup T (F : nat -> set T) n i : (i < n)%N ->
  F i `<=` \big[setU/set0]_(j < n) F j.
Proof. by move: n => // n ni; rewrite -bigcup_mkord; exact/bigcup_sup. Qed.

HB.mixin Record isFiniteSignedMeasure d (R : numFieldType)
  (T : semiRingOfSetsType d) (mu : set T -> \bar R) := {
    isfinite : forall U, measurable U -> mu U \is a fin_num}.

HB.structure Definition FiniteSignedMeasure d
    (R : numFieldType) (T : semiRingOfSetsType d) := {
  mu of isFiniteSignedMeasure d R T mu }.

HB.mixin Record isAdditiveSignedMeasure d (R : numFieldType)
    (T : semiRingOfSetsType d) mu of isFiniteSignedMeasure d R T mu := {
  smeasure_semi_additive : semi_additive mu }.

HB.structure Definition AdditiveSignedMeasure d (R : numFieldType)
    (T : semiRingOfSetsType d) :=
  { mu of isAdditiveSignedMeasure d R T mu & FiniteSignedMeasure d mu }.

Notation additive_smeasure := AdditiveSignedMeasure.type.
Notation "{ 'additive_smeasure' 'set' T '->' '\bar' R }" :=
  (additive_smeasure R T) (at level 36, T, R at next level,
    format "{ 'additive_smeasure'  'set'  T  '->'  '\bar'  R }") : ring_scope.

HB.mixin Record isSignedMeasure0 d (R : numFieldType) (T : semiRingOfSetsType d)
    mu of isAdditiveSignedMeasure d R T mu & isFiniteSignedMeasure d R T mu := {
  smeasure_semi_sigma_additive : semi_sigma_additive mu }.

HB.structure Definition SignedMeasure d (R : numFieldType)
    (T : semiRingOfSetsType d) :=
  { mu of isSignedMeasure0 d R T mu & AdditiveSignedMeasure d mu }.

Notation smeasure := SignedMeasure.type.
Notation "{ 'smeasure' 'set' T '->' '\bar' R }" := (smeasure R T)
  (at level 36, T, R at next level,
    format "{ 'smeasure'  'set'  T  '->'  '\bar'  R }") : ring_scope.

Lemma s_semi_additiveW d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}) : mu set0 = 0 -> semi_additive mu -> semi_additive2 mu.
Proof.
move=> mu0 amx A B mA mB + AB; rewrite -bigcup2inE bigcup_mkord.
move=> /(amx (bigcup2 A B))->.
- by rewrite !(big_ord_recl, big_ord0)/= adde0.
- by move=> [|[|[]]]//=.
- move=> [|[|i]] [|[|j]]/= _ _ //.
  + rewrite AB.
    by case.
  + rewrite setI0.
    by case.
  + rewrite setIC.
    rewrite AB.
    by case.
  + rewrite setI0.
    by case.
  + rewrite set0I.
    by case.
  + rewrite set0I.
    by case.
  + rewrite setI0.
    by case.
Qed.

Lemma s_measure0 d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}): mu set0 = 0.
Proof.
have /[!big_ord0] ->// := @smeasure_semi_additive _ _ _ mu (fun=> set0) 0%N.
exact: trivIset_set0.
Qed.

Hint Resolve s_measure0 : core.

Hint Resolve smeasure_semi_additive : core.

Lemma s_semi_additive2E d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}) : semi_additive2 mu = additive2 mu.
Proof.
rewrite propeqE; split=> [amu A B ? ? ?|amu A B ? ? _ ?]; last by rewrite amu.
by rewrite amu //; exact: measurableU.
Qed.

Lemma s_measure_semi_additive2 d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}) : semi_additive2 mu.
Proof. apply: s_semi_additiveW => //. Qed.
#[global] Hint Resolve s_measure_semi_additive2 : core.

Lemma s_measureU d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}) : additive2 mu.
Proof. by rewrite -s_semi_additive2E. Qed.

Lemma s_measureDI d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}) (A B : set X) : measurable A -> measurable B ->
  mu A = mu (A `\` B) + mu (A `&` B).
Proof.
move=> mA mB; rewrite -s_measure_semi_additive2.
- by rewrite -setDDr setDv setD0.
- exact: measurableD.
- exact: measurableI.
- by apply: measurableU; [exact: measurableD |exact: measurableI].
- by rewrite setDE setIACA setICl setI0.
Qed.

Lemma s_measureD d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}) (A B : set X) :
  measurable A -> measurable B ->
    (*mu A < +oo ->*) mu (A `\` B) = mu A - mu (A `&` B).
Proof.
move=> mA mB.
rewrite (s_measureDI mu mA mB) addeK// fin_numE 1?gt_eqF 1?lt_eqF//.
- rewrite ltey_eq.
  rewrite isfinite //.
  exact:measurableI.
- rewrite ltNye_eq.
  rewrite isfinite//.
  exact:measurableI.
Qed.

Definition s_mrestr d (T : measurableType d) (R : realFieldType) (D : set T)
  (f : set T -> \bar R) (mD : measurable D) := fun X => f (X `&` D).

Section s_measure_restr.
Variables (d : _) (T : measurableType d) (R : realFieldType).
Variables (mu : {smeasure set T -> \bar R}) (D : set T) (mD : measurable D).

Local Notation restr := (s_mrestr mu mD).

Let s_restr_isfinite U : measurable U -> restr U \is a fin_num.
Proof.
move=> mU.
by have /(@isfinite _ _ _ mu) : measurable (U `&` D) by exact: measurableI.
Qed.

HB.instance Definition _ :=
  isFiniteSignedMeasure.Build _ _ _ restr s_restr_isfinite.

Let s_restr_smeasure_semi_additive : semi_additive restr.
Proof.
move=> F n mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
rewrite -(smeasure_semi_additive _ _ mFD)//; last exact: bigsetU_measurable.
by rewrite /s_mrestr /FD big_distrl.
Qed.

HB.instance Definition _ :=
  isAdditiveSignedMeasure.Build _ _ _ restr s_restr_smeasure_semi_additive.

Let s_restr_smeasure_semi_sigma_additive : semi_sigma_additive restr.
Proof.
move=> F mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
rewrite /restr setI_bigcupl; apply: smeasure_semi_sigma_additive => //.
by apply: bigcup_measurable => k _; exact: measurableI.
Qed.

HB.instance Definition _ :=
  isSignedMeasure0.Build _ _ _ restr s_restr_smeasure_semi_sigma_additive.

End s_measure_restr.

Definition positive_set d (R : realType) (X : measurableType d)
             (nu : {smeasure set X -> \bar R}) (P : set X):=
               (P \in measurable) /\
                 forall E, (E \in measurable) -> (E `<=` P) -> (nu E >= 0)%E.
Definition negative_set d (R : realType) (X : measurableType d)
             (nu : {smeasure set X -> \bar R}) (N : set X):=
               (N \in measurable) /\
                 forall E, (E \in measurable) -> (E `<=` N) -> (nu E <= 0)%E.

Lemma subset_nonnegative_set d (R : realType) (X : measurableType d)
             (nu : {smeasure set X -> \bar R}) (N M : set X) : (M `<=` N) ->
              (nu N < 0)%E -> (nu M > 0)%E -> (~ negative_set nu N) -> (~ negative_set nu (N `\` M)).
Abort.

Lemma negative_set0 d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) : negative_set nu set0.
Proof.
rewrite /negative_set.
rewrite inE.
split => // E _.
rewrite subset0 => ->.
by rewrite s_measure0.
Qed.

(* TODO: PR *)
Lemma lt_trivIset T (F : nat -> set T) :
  (forall n m, (m < n)%N -> F m `&` F n = set0) -> trivIset setT F.
Proof.
move=> h; apply/trivIsetP => m n _ _; rewrite neq_lt => /orP[|]; first exact: h.
by rewrite setIC; exact: h.
Qed.

(* TODO: PR *)
Lemma subsetC_trivIset T (F : nat -> set T) :
  (forall n, F n.+1 `<=` ~` \big[setU/set0]_(i < n.+1) F i) -> trivIset setT F.
Proof.
move=> ACU; apply: lt_trivIset => n m mn; rewrite setIC; apply/disjoints_subset.
case: n mn => // n mn.
by apply: (subset_trans (ACU n)); exact/subsetC/bigsetU_sup.
Qed.

(* TODO: PR *)
Lemma fin_num_ltey (R : realDomainType) (x : \bar R) : x \is a fin_num -> x < +oo.
Proof. by move: x => [r| |]// _; rewrite ltey. Qed.

(* TODO: PR *)
Lemma gt0_fin_numE {R : realDomainType} [x : \bar R] : 0 < x -> (x \is a fin_num) = (x < +oo).
Proof. by rewrite lt_neqAle => /andP[_]; exact: ge0_fin_numE. Qed.

Lemma negative_set_smeasure0 d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
  forall N, negative_set nu N -> nu N <= 0.
Proof. by move=> N [mN]; exact. Qed.

Lemma negative_set_bound d (R : realType) (X : measurableType d)
    (nu : {smeasure set X -> \bar R}) S : measurable S ->
  ~ negative_set nu S -> exists l,
    (l != 0%N) &&
    `[< exists F, [/\ F `<=` S, measurable F & nu F >= l%:R^-1%:E] >].
Proof.
move=> mS=> /not_andP[/[1!inE]//|].
move=> /existsNP[F] /not_implyP[/[1!inE] mF] /not_implyP[FS].
move/negP; rewrite -ltNge => nuF0.
exists `|ceil (fine(nu F))^-1|%N; apply/andP; split.
  rewrite -lt0n absz_gt0 gt_eqF// ceil_gt0// invr_gt0// fine_gt0// nuF0/=.
  by rewrite fin_num_ltey// isfinite.
apply/asboolP; exists F; split => //.
rewrite natr_absz ger0_norm; last by rewrite ceil_ge0// invr_ge0 fine_ge0 ?ltW.
rewrite -[leRHS](@fineK _ (nu F)) ?isfinite// lee_fin.
rewrite -[leRHS](invrK (fine (nu F))) ler_pinv; last 2 first.
    rewrite inE unitfE andb_idl; last by move=> ?; rewrite gt_eqF.
    rewrite ltr0z ceil_gt0// invr_gt0// fine_gt0// nuF0/= fin_num_ltey//.
    by rewrite isfinite.
  rewrite inE unitfE andb_idl; last by move/gt_eqF/negbT.
  by rewrite invr_gt0 fine_gt0// nuF0/= fin_num_ltey// isfinite.
by rewrite ceil_ge// ceil_ge0// invr_ge0 fine_ge0// ltW.
Qed.

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
      by apply: inv_cvg => // n; rewrite ltr0n lt0n spos.
    apply/(@cvg_series_cvg_0 _ [normedModType R of R^o])/nneseries_is_cvg => //.
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
    rewrite s_measureD// setIidr// suber_lt0 ?isfinite//.
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
    by rewrite lt_eqF// s_measureD// setIidr// suber_lt0 ?isfinite// (lt_le_trans nuS0).
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
    rewrite s_measureU//; first by rewrite adde_ge0// (le_trans _ s1F1).
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
    apply: inv_cvg => // m.
    by rewrite lt_neqAle eq_sym pnatr_eq0 elt_s0/= ler0n.
  apply: (@cvg_series_cvg_0 _ [normedModType R of R^o]); apply: nneseries_is_cvg => //.
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
  (forall N, measurable N -> negative_set nu (N `&` P) -> s_mrestr nu mP N = 0) ->
    forall S, S \in measurable -> S `<=` P -> s_mrestr nu mP S >= 0.
Proof.
move=> h S /[1!inE] mS SP.
pose mu := [the smeasure _ _ of s_mrestr nu mP].
have : forall N, negative_set mu N -> mu N = 0.
  move=> N [/[1!inE] mN Nmu]; rewrite /mu/= h//; split=> [|E /[1!inE] mE ENP].
    by rewrite inE; exact: measurableI.
  have : E `&` P `<=` N by move=> x [Ex Px]; have [] := ENP x Ex.
  have : measurable (E `&` P) by exact: measurableI.
  rewrite -inE => /Nmu /[apply].
  rewrite /mu/= /s_mrestr/=.
  suff -> : E `&` P `&` P = E by [].
  rewrite -setIA setIid; apply/seteqP; split=> [x []//|x Ex].
  by have [] := ENP _ Ex.
by move/(@positive_set_0 _ _ _ mu); exact.
Qed.


Lemma positive_negative0  d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
    forall P N, positive_set nu P -> negative_set nu N ->
            forall S, measurable S -> nu (S `&` P `&` N) = 0.
Proof.
move=> P N [mP posP] [mN negN] S mS.
rewrite !inE in mP mN mS.
apply /eqP.
rewrite eq_le.
apply /andP; split.
  apply negN.
    rewrite inE.
    apply measurableI => //; apply: measurableI => //.
  apply setIidPl.
  by rewrite -setIA setIid.
rewrite -setIAC.
apply posP.
  rewrite inE.
  apply measurableI => //; apply measurableI => //.
apply setIidPl.
by rewrite -setIA setIid.
Qed.

Lemma s_measure_partition2 d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
    forall P N, measurable P -> measurable N -> P `|` N = setT -> P `&` N = set0 ->
      forall S, measurable S -> nu S = nu (S `&` P) + nu (S `&` N).
Proof.
move=> P N mP mN PNT PN0 S mS.
rewrite -{1}(setIT S) -PNT setIUr s_measureU//.
  1,2:by apply measurableI.
by rewrite setICA -(setIA S P N) PN0 setIA setI0.
Qed.

Section hahn_decomposition_lemma.
Variables (d : _) (X : measurableType d) (R : realType).
Variables (mu : {smeasure set X -> \bar R}).

Variable D : set X.

Let elt_prop (x : set X * \bar R * set X) :=
  [/\ measurable x.1.1,
     0 <= mu x.1.1,
     0 <= x.1.2,
     x.1.1 `<=` D &
     mu x.1.1 >= mine (x.1.2 * 2^-1%:E) 1].

Let elt_type := {x | elt_prop x}.

Let A_ (x : elt_type) := (proj1_sig x).1.1.
Let d_ (x : elt_type) := (proj1_sig x).1.2.
Let U_ (x : elt_type) := (proj1_sig x).2.

Let elt_mA (x : elt_type) : measurable (A_ x).
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let elt_A_ge0 (x : elt_type) : 0 <= mu (A_ x).
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let elt_d_ge0 (x : elt_type) : 0 <= d_ x.
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let elt_mine (x : elt_type) : mu (A_ x) >= mine (d_ x * 2^-1%:E) 1.
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let elt_D (x : elt_type) : A_ x `<=` D.
Proof. by move: x => [[[? ?] ?]] []. Qed.

Let set_mE A := [set mE | exists E, [/\ mE = mu E, measurable E & E `<=` D `\` A] ].

Let dd A := ereal_sup (set_mE A).

Let seq_sup (a b : elt_type) :=
  [/\ d_ b = dd (U_ a), A_ b `<=` D `\` U_ a & U_ b = U_ a `|` A_ b ].

Let next_elt A : 0 <= dd A -> {B | [/\ measurable B,
  mu B >= 0, B `<=` D `\` A & mu B >= mine (dd A * 2^-1%:E) 1]}.
Proof.
move=> d_ge0.
pose m := mine (dd A * 2^-1%R%:E) 1%E.
apply/cid.
move: d_ge0; rewrite le_eqVlt => /predU1P[<-|d_gt0].
  by exists set0; split => //; rewrite s_measure0.
have m_gt0 : 0 < m by rewrite /m lt_minr lte01 andbT mule_gt0.
have : m < dd A.
  rewrite /m; have [->|dn1oo] := eqVneq (dd A) +oo.
    by rewrite min_r// ?ltey// gt0_mulye// leey.
  rewrite -(@fineK _ (dd A)); last first.
    by rewrite ge0_fin_numE// ?(ltW d_gt0)// lt_neqAle dn1oo leey.
  rewrite -EFinM minEFin lte_fin lt_minl; apply/orP; left.
  rewrite ltr_pdivr_mulr// ltr_pmulr// ?ltr1n// fine_gt0// d_gt0/=.
  by rewrite lt_neqAle dn1oo/= leey.
move=> /ereal_sup_gt/cid2[x/= /cid[B [-> mB BDA mmuB]]].
exists B; split => //.
  by rewrite (le_trans _ (ltW mmuB))// ltW.
by rewrite (le_trans _ (ltW mmuB)).
Qed.

Lemma hahn_decomposition_lemma : measurable D -> mu D <= 0 ->
  {A | [/\ A `<=` D, measurable A, negative_set mu A & mu A <= mu D] }.
Proof.
move=> mD muD_ge0.
have d0_ge0 : 0 <= dd set0.
  by apply: ereal_sup_ub => /=; exists set0; split => //; rewrite s_measure0.
have [A0 [mA0 muA0 + A0d0]] := next_elt d0_ge0.
rewrite setD0 => A0D.
have [v [v0 Pv]] : {v : nat -> elt_type |
    v 0%N = exist _ (A0, dd set0, A0) (And5 mA0 muA0 d0_ge0 A0D A0d0) /\
    forall n, seq_sup (v n) (v n.+1)}.
  apply dependent_choice_Type => -[[[A' ?] U] [/= mA' mA'0]].
  have d1_ge0 : 0 <= dd U.
    by apply: ereal_sup_ub => /=; exists set0; split => //; rewrite s_measure0.
  have [A1 [mA1 muA10 A1DU A1d1] ] := next_elt d1_ge0.
  have A1D : A1 `<=` D by apply: (subset_trans A1DU); apply: subDsetl.
  by exists (exist _ (A1, dd U, U `|` A1) (And5 mA1 muA10 d1_ge0 A1D A1d1)).
set Aoo := \bigcup_k A_ (v k).
have mA_ k : d.-measurable (A_ (v k)) by exact: elt_mA.
have mAoo : measurable Aoo by exact: bigcup_measurable.
have Ubig n : U_ (v n) = \big[setU/set0]_(i < n.+1) A_ (v i).
  elim: n => [|n ih]; first by rewrite v0/= big_ord_recr/= big_ord0 set0U v0.
  by have [_ _ ->] := Pv n; rewrite big_ord_recr/= -ih.
have tA : trivIset setT (A_ \o v).
  apply: subsetC_trivIset => n.
  have [_ + _] := Pv n.
  move/subset_trans; apply.
  rewrite -setTD.
  apply: setDSS => //.
  by rewrite Ubig big_ord_recr.
exists (D `\` Aoo).
have cvg_muA : (fun n => \sum_(0 <= i < n) mu (A_ (v i))) --> mu Aoo.
  exact: smeasure_semi_sigma_additive.
have muAoo : 0 <= mu Aoo.
  move/cvg_lim : cvg_muA => <-//=; apply: nneseries_ge0 => n _.
  exact: elt_A_ge0.
have A_cvg_0 : (fun n => mu (A_ (v n))) --> 0.
  rewrite [X in X --> _](_ : _ = EFin \o (fun n => fine (mu (A_ (v n))))); last first.
    by apply/funext => n/=; rewrite fineK// isfinite.
  apply: continuous_cvg => //.
  apply/(@cvg_series_cvg_0 _ [normedModType R of R^o]).
  move: cvg_muA.
  rewrite -(@fineK _ (mu Aoo)) ?isfinite//.
  move/ereal_cvg_real => [_ ?].
  rewrite (_ : series _ = fine \o (fun n => \sum_(0 <= i < n) mu (A_ (v i)))); last first.
    apply/funext => n /=.
    by rewrite /series/= sum_fine//= => i _; rewrite isfinite.
  by apply/cvg_ex; exists (fine (mu Aoo)).
have mine_cvg_0 : (fun n => mine (d_ (v n) * 2^-1%:E) 1) --> 0.
  apply: (@ereal_squeeze _ (cst 0) _ (fun n => mu (A_ (v n)))); [|exact: cvg_cst|by []].
  apply: nearW => n /=.
  by rewrite elt_mine andbT le_minr lee01 andbT mule_ge0.
have d_cvg_0 : d_ \o v --> 0.
  move/ereal_cvg_real : A_cvg_0 => -[_].
  move/(@cvg_distP _ [normedModType R of R^o]) => /(_ _ ltr01).
  rewrite near_map => -[N _ hN].
  have d_v_fin_num : \forall x \near \oo, d_ (v x) \is a fin_num.
    near=> n.
    have /hN : (N <= n)%N by near: n; exists N.
    rewrite sub0r normrN /= ger0_norm ?fine_ge0//.
    have := elt_mine (v n).
    rewrite /mine; case: ifPn => [+ _ _|].
      rewrite lte_pdivr_mulr// mul1e => d2.
      by rewrite ge0_fin_numE// (lt_le_trans d2)// leey.
    move=> _ /[swap]; rewrite ltNge => -/[swap].
    by move/fine_le => -> //; rewrite isfinite.
  apply/ereal_cvg_real; split => //.
  apply/(@cvg_distP _ [normedModType R of R^o]) => e e0.
  rewrite near_map.
  move/ereal_cvg_real : mine_cvg_0 => -[_].
  move/(@cvg_distP _ [normedModType R of R^o]).
  have : (0 < minr (e / 2) 1)%R by rewrite lt_minr// ltr01 andbT divr_gt0.
  move=> /[swap] /[apply].
  rewrite near_map => -[M _ hM].
  near=> n.
  rewrite sub0r normrN.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN /mine/=; case: ifPn => [_|].
    rewrite fineM//=; last by near: n; exact: d_v_fin_num.
    rewrite normrM (@gtr0_norm _ 2^-1%R); last by rewrite invr_gt0.
    rewrite ltr_pdivr_mulr//.
    move/lt_le_trans; apply.
    rewrite /minr; case: ifPn.
      by rewrite -mulrA mulVr// ?mulr1// unitfE.
    by rewrite -leNgt -ler_pdivl_mulr.
  rewrite -leNgt /minr; case: ifPn.
    by rewrite ger0_norm//= => /ltW e21 _; rewrite ltNge e21.
  by rewrite ger0_norm//= ltxx.
have muDAoo : mu D >= mu (D `\` Aoo).
  rewrite -[in leRHS](@setDUK _ Aoo D); last by apply: bigcup_sub => i _; exact: elt_D.
  rewrite s_measureU//; last 2 first.
    exact: measurableD.
    by rewrite setDIK.
  by rewrite lee_addr.
split; [by []|exact: measurableD| | by []].
split; first by rewrite inE; exact: measurableD.
move=> E /[1!inE] mE EDAoo.
pose H n := set_mE (\big[setU/set0]_(i < n) A_ (v i)).
have EH n : [set mu E] `<=` H n.
  have : mu E \in set_mE Aoo by rewrite inE; exists E.
  rewrite -sub1set => /subset_trans; apply.
  move=> x/= [F [? ? FB]].
  exists F; split => //.
  apply: (subset_trans FB).
  by apply: setDS; exact: bigsetU_bigcup.
have mudelta n : mu E <= d_ (v n).
  move: n => [|n].
    rewrite v0/=.
    apply: ereal_sup_ub => /=; exists E; split => //.
    by apply: (subset_trans EDAoo); exact: setDS.
  suff : mu E <= dd (U_ (v n)) by have [<- _] := Pv n.
  have /le_ereal_sup := EH n.+1.
  rewrite ereal_sup1 => /le_trans; apply.
  apply/le_ereal_sup => x/= [A' [? ? A'D]].
  exists A'; split => //.
  apply: (subset_trans A'D).
  by apply: setDS; rewrite Ubig.
apply: (@closed_cvg _ _ _ _ _ (fun v => mu E <= v) _ _ _ d_cvg_0) => //.
  exact: closed_ereal_le_ereal.
exact: nearW.
Unshelve. all: by end_near. Qed.

End hahn_decomposition_lemma.

(* TODO: rename seqDUE to seqDU_seqD *)
Lemma seqDUE' X (S : set X) (F : (set X)^nat) :
  (fun n => S `&` F n `\` \bigcup_(i in `I_n) F i) = seqDU (fun n => S `&` F n).
Proof.
apply/funext => n; rewrite -setIDA; apply/seteqP; split.
  move=> x [Sx [Fnx UFx]]; split=> //; apply: contra_not UFx => /=.
  by rewrite bigcup_mkord -big_distrr/= => -[].
by rewrite /seqDU -setIDA bigcup_mkord -big_distrr/= setDIr setIUr setDIK set0U.
Qed.

Lemma bigcup_negative_set d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) (F : (set X)^nat) :
  (forall i, negative_set nu (F i)) ->
  negative_set nu (\bigcup_i F i).
Proof.
move=> H.
have mUF : measurable (\bigcup_i F i).
  by apply: bigcup_measurable => n _; have [/[1!inE]] := H n.
split=> [/[1!inE]//| S /[1!inE] mS SUF].
pose SF n := (S `&` F n) `\` \bigcup_(i in `I_n) F i.
have SFE : SF = seqDU (fun n => S `&` F n) by rewrite -seqDUE'.
have tS_ : trivIset setT SF by rewrite SFE; exact: trivIset_seqDU.
have SSF : S = \bigcup_i SF i.
  transitivity (\bigcup_i seqDU (fun n => S `&` F n) i); last first.
    by apply: eq_bigcup => // n _; rewrite SFE.
  by rewrite -seqDU_bigcup_eq -setI_bigcupr setIidl.
have mSF : forall n, measurable (SF n).
  move=> n; rewrite /SF; apply: measurableD.
    by apply: measurableI => //; have [/[1!inE]] := H n.
  by apply: bigcup_measurable => // k _; have [/[1!inE]] := H k.
have SFS : (fun n => \sum_(0 <= i < n) nu (SF i)) --> nu S.
  rewrite SSF; apply: smeasure_semi_sigma_additive => //.
  exact: bigcup_measurable.
have nuS_ n : nu (SF n) <= 0.
  have [_] := H n.
  by apply; rewrite ?inE// => x -[[]].
move/cvg_lim : (SFS) => <-//.
apply: ereal_lim_le.
  by apply/cvg_ex => /=; first eexists; exact: SFS.
by apply: nearW => n; exact: sume_le0.
Qed.

Lemma negative_setU d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) N M :
  negative_set nu N -> negative_set nu M -> negative_set nu (N `|` M).
Proof.
move=> nN nM.
rewrite -bigcup2E.
apply: bigcup_negative_set => -[//|[//|/= _]].
exact: negative_set0.
Qed.

Section hahn_decomposition.
Variables (d : _) (X : measurableType d) (R : realType).
Variable nu : {smeasure set X -> \bar R}.

Let elt_prop (A : set X * \bar R * set X) :=
  [/\ measurable A.1.1,
     nu A.1.1 <= 0,
     A.1.2 <= 0,
     negative_set nu A.1.1 &
     nu A.1.1 <= maxe (A.1.2 * 2^-1%:E) (- ( 1)) ].

Let elt_type := {x | elt_prop x}.

Let A_ (x : elt_type) := (proj1_sig x).1.1.
Let s_ (x : elt_type) := (proj1_sig x).1.2.
Let U_ (x : elt_type) := (proj1_sig x).2.

Let elt_mA (x : elt_type) : measurable (A_ x).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let elt_nuA (x : elt_type) : nu (A_ x) <= 0.
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let elt_s (x : elt_type) : s_ x <= 0.
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let elt_neg_set (x : elt_type) : negative_set nu (A_ x).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let elt_maxe (x : elt_type) : nu (A_ x) <= maxe (s_ x * 2^-1%:E) (- ( 1)).
Proof. by move: x => [[[? ?] ?]] -[]. Qed.

Let set_mE A :=
  [set mE | exists E, [/\ mE = nu E, measurable E & E `<=` setT `\` A] ].

Let ss A := ereal_inf (set_mE A).

Let seq_inf (a b : elt_type) :=
  [/\ s_ b = ss (U_ a), A_ b `<=` setT `\` U_ a & U_ b = U_ a `|` A_ b].

Let next_elt A : ss A <= 0 -> {B |
  [/\ measurable B, nu B <= 0, B `<=` setT `\` A, negative_set nu B &
     nu B <= maxe (ss A * 2^-1%R%:E) (- 1%E)] }.
Proof.
move=> s_le0.
pose m := maxe (ss A * 2^-1%R%:E) (- 1%E).
apply/cid.
move: s_le0; rewrite le_eqVlt => /predU1P[->|s_lt0].
  by exists set0; split => //; rewrite ?s_measure0//; exact: negative_set0.
have m0_lt0 : m < 0 by rewrite /m lt_maxl lteN10 andbT nmule_rlt0.
have : ss A < m.
  rewrite /m; have [->|s0oo] := eqVneq (ss A) -oo.
    by rewrite max_r ?ltNye// gt0_mulNye// leNye.
  rewrite -(@fineK _ (ss A)); last first.
    by rewrite le0_fin_numE// ?(ltW s_lt0)// lt_neqAle leNye eq_sym s0oo.
  rewrite -EFinM maxEFin lte_fin lt_maxr; apply/orP; left.
  rewrite ltr_pdivl_mulr// gtr_nmulr ?ltr1n// fine_lt0// s_lt0/=.
  by rewrite lt_neqAle s0oo/= leNye.
move=> /ereal_inf_lt/cid2[_/= /cid[B [-> mB BA nuBm]]].
have nuB_le0 : nu B <= 0.
  by rewrite (le_trans (ltW nuBm))// ltW.
have [C [CB mN1 neg_set_C nuCnuB]] := hahn_decomposition_lemma mB nuB_le0.
exists C; split => //.
- by rewrite (le_trans nuCnuB).
- exact: (subset_trans CB).
- by rewrite (le_trans nuCnuB)// (le_trans (ltW nuBm)).
Qed.

Theorem Hahn_decomposition : exists P N,
   [/\ positive_set nu P, negative_set nu N, P `|` N = setT & P `&` N = set0].
Proof.
have s0_le0 : ss set0 <= 0.
  by apply: ereal_inf_lb => /=; exists set0; split => //; rewrite s_measure0.
have [A0 [mA0 muA0_le0 _ neg_set_A0 A0d0]] := next_elt s0_le0.
have [v [v0 Pv]] : {v : nat -> elt_type |
    v 0%N = exist _ (A0, ss set0, A0) (And5 mA0 muA0_le0 s0_le0 neg_set_A0 A0d0) /\
    forall n, seq_inf (v n) (v n.+1)}.
  apply dependent_choice_Type => -[[[A' d'] U'] [/= mAn [nuAn_le0 neg_set_An]]].
  pose sn1 := ss U'.
  have sn1_le0 : sn1 <= 0.
    by apply: ereal_inf_lb => /=; exists set0; split => //; rewrite s_measure0.
  have [A1 [mA1 nuA1_le0 A1U' neg_set_A1 A1d1] ] := next_elt sn1_le0.
  by exists (exist _ (A1, sn1, U' `|` A1) (And5 mA1 nuA1_le0 sn1_le0 neg_set_A1 A1d1)).
set N := \bigcup_k (A_ (v k)).
have mN : measurable N by exact: bigcup_measurable.
have Ubig n : U_ (v n) = \big[setU/set0]_(i < n.+1) A_ (v i).
  elim: n => [|n ih]; first by rewrite v0/= big_ord_recr/= big_ord0 set0U v0.
  by have [_ _ ->] := Pv n; rewrite big_ord_recr/= -ih.
have tA : trivIset setT (A_ \o v).
  apply: subsetC_trivIset => n.
  have [_ + _] := Pv n.
  move/subset_trans; apply.
  rewrite -setTD.
  apply: setDSS => //.
  by rewrite Ubig big_ord_recr.
have neg_set_N : negative_set nu N.
  by apply: bigcup_negative_set => i; exact: elt_neg_set.
pose P := setT `\` N.
have mP : measurable P by exact: measurableD.
exists P, N; split; first last.
  by rewrite /P setTD setvI.
  by rewrite /P setTD setvU.
  exact: neg_set_N.
rewrite /positive_set inE; split=> // D; rewrite inE => mD DP; rewrite leNgt; apply/negP => nuD0.
have snuD n : s_ (v n) <= nu D.
  move: n => [|n].
    by rewrite v0 /=; apply: ereal_inf_lb => /=; exists D; rewrite setD0.
  have [-> _ _] := Pv n.
  apply: ereal_inf_lb => /=; exists D; split => //.
  apply: (subset_trans DP).
  apply: setDS.
  by rewrite Ubig; exact: bigsetU_bigcup.
have max_le0 n : maxe (s_ (v n) * 2^-1%:E) (- (1)) <= 0.
  rewrite /maxe; case: ifPn => // _.
  by rewrite pmule_lle0// (le_trans (snuD _))// ltW.
have not_s_cvg_0 : ~ s_ \o v --> 0.
  move/ereal_cvg_real => -[sfin].
  move/(@cvg_distP _ [normedModType R of R^o]).
  have : (0 < `|fine (nu D)|)%R by rewrite normr_gt0// fine_eq0// ?lt_eqF// isfinite.
  move=> /[swap] /[apply].
  rewrite near_map => -[M _ hM].
  near \oo => n.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN /= ler0_norm//; last by rewrite fine_le0.
  rewrite ltr0_norm//; last by rewrite fine_lt0// nuD0 andbT ltNye_eq isfinite.
  rewrite ltr_opp2; apply/negP; rewrite -leNgt; apply: fine_le.
  - near: n; exact.
  - by rewrite isfinite.
  - exact: snuD.
have nuN : nu N = \sum_(n <oo) nu (A_ (v n)).
  apply/esym/cvg_lim => //.
  by apply: smeasure_semi_sigma_additive; [by []|exact: tA|exact: bigcup_measurable].
have sum_A_maxe : \sum_(n <oo) nu (A_ (v n)) <= \sum_(n <oo) maxe (s_ (v n) * 2^-1%:E) (- (1)).
  exact: lee_npeseries.
have : cvg (fun n => \sum_(0 <= k < n) maxe (s_ (v k) * 2^-1%:E) (- (1))).
  by apply: is_cvg_ereal_npos_natsum_cond => n _ _; exact: max_le0.
move=> /cvg_ex[[l| |]]; first last.
  - move/cvg_lim => limNoo.
    have : nu N <= -oo by rewrite -limNoo// nuN.
    rewrite leeNy_eq => /eqP nuNoo.
    have := @isfinite _ _ _ nu N mN.
    by rewrite fin_numE => /andP[+ _] => /eqP; apply.
  - move/cvg_lim => limoo.
    have := @npeseries_le0 _ (fun n => maxe (s_ (v n) * 2^-1%:E) (- (1))) xpredT.
    rewrite limoo// leNgt.
    by move=> /(_ (fun n _ => max_le0 n))/negP; apply.
move/ereal_cvg_real => [Hfin cvgl].
have : cvg (series (fun n => fine (maxe (s_ (v n) * 2^-1%:E) (- (1))))).
  apply/cvg_ex; exists l.
  move: cvgl.
  rewrite [X in X --> _](_ : _ =
    (fun n => \sum_(0 <= k < n) fine (maxe (s_ (v k) * 2^-1%:E)%E (- (1))%E))%R) //.
  apply/funext => n/=.
  rewrite sum_fine// => i _.
  rewrite le0_fin_numE.
    by rewrite (lt_le_trans _ (elt_maxe _))// -le0_fin_numE// ?isfinite.
  by rewrite /maxe; case: ifPn => // _; rewrite mule_le0_ge0.
move/(@cvg_series_cvg_0 _ [normedModType R of R^o]) => maxe_cvg_0.
apply: not_s_cvg_0.
rewrite [X in X --> _](_ : _ = (fun n => s_ (v n) * 2^-1%:E) \* cst 2%:E); last first.
  apply/funext => n/=.
  by rewrite -muleA -EFinM mulVr ?mule1// unitfE.
rewrite (_ : 0 = 0 * 2%:E); last by rewrite mul0e.
apply: ereal_cvgM; [by rewrite mule_def_fin| |exact: cvg_cst].
apply/ereal_cvg_real; split.
  move/(@cvg_distP _ [normedModType R of R^o]) : maxe_cvg_0 => /(_ _ ltr01).
  rewrite near_map => -[M _ hM].
  near=> n.
  have /hM : (M <= n)%N by near: n; exists M.
  rewrite sub0r normrN => maxe_lt1.
  rewrite fin_numE; apply/andP; split.
    apply/negP => /eqP h.
    by rewrite h max_r// ?leNye//= normrN normr1 ltxx in maxe_lt1.
  by rewrite lt_eqF// (@le_lt_trans _ _ 0)// mule_le0_ge0.
apply/(@cvg_distP _ [normedModType R of R^o]) => e e0.
rewrite near_map.
move/(@cvg_distP _ [normedModType R of R^o]) : maxe_cvg_0.
have : (0 < minr e 1)%R by rewrite lt_minr// e0 ltr01.
move=> /[swap] /[apply].
rewrite near_map => -[M _ hM].
near=> n.
rewrite sub0r normrN.
have /hM : (M <= n)%N by near: n; exists M.
rewrite sub0r normrN.
rewrite /maxe/=; case: ifPn => [_|].
  rewrite normrN normr1 /minr.
  by case: ifPn; rewrite ?ltxx// ltNge => /[swap] /ltW ->.
rewrite -leNgt => ?.
move/lt_le_trans; apply.
rewrite /minr; case: ifPn => //.
by rewrite -leNgt.
Unshelve. all: by end_near. Qed.

End hahn_decomposition.

Definition is_Hahn_decomposition d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :=
  fun P N =>
   [/\ positive_set nu P,
      negative_set nu N,
      P `|` N = setT &
      P `&` N = set0].

(* memo : trying to auto resolve a following lemma but it doesn't work *)
(*
Lemma positive_set_is_measurable d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
      forall P, positive_set nu P -> measurable P.
Proof.
move=> P [mP _].
by rewrite inE in mP.
Qed.

Hint Resolve positive_set_is_measurable.
*)

Lemma Hahn_decomposition_measure_uniqueness
  d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
  forall P1 N1 P2 N2,
   is_Hahn_decomposition nu P1 N1 -> is_Hahn_decomposition nu P2 N2 ->
   forall S, measurable S ->
          nu (S `&` P1) = nu (S `&` P2) /\ nu (S `&` N1) = nu (S `&` N2).
Proof.
move=> P1 N1 P2 N2 Hahn1 Hahn2 S mS.
move: (Hahn1) (Hahn2) => [posP1 negN1 PN1T PN10] [posP2 negN2 PN2T PN20].
move: (posP1) (negN1) (posP2) (negN2) => [mP1 _] [mN1 _] [mP2 _] [mN2 _].
rewrite !inE in mP1 mN1 mP2 mN2.
have mSP1 := (measurableI S P1 mS mP1).
have mSN1 := (measurableI S N1 mS mN1).
have mSP2 := (measurableI S P2 mS mP2).
have mSN2 := (measurableI S N2 mS mN2).
split.
  apply (@eq_trans _ _ (nu (S `&` P1 `&` P2))).
     by rewrite (s_measure_partition2 nu mP2 mN2 PN2T PN20)//
       (positive_negative0 posP1 negN2 mS) adde0.
   by rewrite [RHS](s_measure_partition2 nu mP1 mN1 PN1T PN10)//
     (positive_negative0 posP2 negN1 mS) adde0 setIAC.
apply (@eq_trans _ _ (nu (S `&` N1 `&` N2))).
   by rewrite (s_measure_partition2 nu mP2 mN2 PN2T PN20)//
     {1}setIAC (positive_negative0 posP2 negN1 mS) add0e.
 by rewrite [RHS](s_measure_partition2 nu mP1 mN1 PN1T PN10)//
   (setIAC _ _ P1) (positive_negative0 posP1 negN2 mS) add0e setIAC.
Qed.

(* TODO: PR *)
Section maxe_monoid.
Context {R : realDomainType}.

Lemma maxeA : associative (S := \bar R) maxe.
Proof. exact maxA. Qed.

Lemma maxNye : left_id (-oo : \bar R) maxe.
Proof. move=> x. rewrite maxC. exact : maxeNy. Qed.

Canonical maxe_monoid := Monoid.Law maxeA maxNye maxeNy.
End maxe_monoid.

Lemma bigmax_lee (R : realType)
    : forall (F : (\bar R)^nat) (n m : nat), (n <= m)%nat ->
  \big[maxe/-oo]_(j < n) F j <=
  \big[maxe/-oo]_(j < m) F j.
Proof.
move=> F n m nm.
rewrite -[in leRHS](subnKC nm).
rewrite -[in leRHS](big_mkord xpredT F).
rewrite/index_iota.
rewrite subn0.
rewrite iotaD.
rewrite big_cat /=.
rewrite le_maxr.
apply /orP.
left.
rewrite -[in iota _ _](subn0 n).
by rewrite big_mkord.
Qed.
(*
Section discrete_measurable_rat.

Definition discrete_measurable_rat : set (set rat) := [set: set rat].

Let discrete_measurable_rat0 : discrete_measurable_rat set0. Proof. by []. Qed.

Let discrete_measurable_ratC X :
  discrete_measurable_rat X -> discrete_measurable_rat (~` X).
Proof. by []. Qed.

Let discrete_measurable_ratU (F : (set rat)^nat) :
  (forall i, discrete_measurable_rat (F i)) ->
  discrete_measurable_rat (\bigcup_i F i).
Proof. by []. Qed.

HB.instance Definition _ := @isMeasurable.Build default_measure_display rat
  (Pointed.class _) discrete_measurable_rat discrete_measurable_rat0
  discrete_measurable_ratC discrete_measurable_ratU.

End discrete_measurable_rat.
*)
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
apply : measurableD.

Lemma measurable_eq_fun d (X : measurableType d) (R : realType) (f g : X -> \bar R) :
   measurable_fun setT f -> measurable_fun setT g -> measurable [set x | f x = g x].
Proof.

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



(* --- *)

Theorem Radon_Nikodym_finite_nonnegative d (X : measurableType d) (R : realType)
    (mu nu : {measure set X -> \bar R})
    (mufinite : (mu setT < +oo)%E) (nufinite : (nu setT < +oo)%E) :
  nu `<< mu -> exists f : X -> \bar R, [/\
        forall x, f x >= 0,
        integrable mu setT f &
        forall E, E \in measurable -> nu E = \int[mu]_(x in E) f x].
Proof.
(*
 * Define the measurable subsets of X to be those subsets that belong to the
 *  σ-algebra measurable on which the measures mu and nu are defined.
 *)
move=> mudomnu.
pose G := [set g : X -> \bar R | [/\
  forall x, (g x >= 0)%E,
  integrable mu setT g &
  forall E, E \in measurable -> (\int[mu]_(x in E) g x <= nu E)%E] ].
(* maybe define G : set R insted of set \bar R
pose G' := [set g : X -> \bar R |
            [/\ (forall x, (g x >= 0)%E),
               integrable mu setT g &
                 forall E, E \in measurable -> fine (\int[mu]_(x in E) g x) <= fine (nu E) ] ].
*)
have neG : G !=set0.
  exists (cst 0%E); split; first by [].
  - exact: integrable0.
  - by move=> E _; by rewrite integral0.
pose IG := [set \int[mu]_x g x | g in G]%E.
have neIG : IG !=set0.
  case: neG => g [g0 g1 g2].
  by exists (\int[mu]_x g x)%E, g.
have IGbound : exists M, forall x, x \in IG -> (x <= M%:E)%E.
  exists (fine (nu setT)) => x.
  rewrite inE => -[g [g0 g1 g2] <-{x}].
  rewrite fineK; last by rewrite ge0_fin_numE.
  by rewrite (le_trans (g2 setT _))// inE.
pose M := ereal_sup IG.
have M0 : 0 <= M.
  rewrite -(ereal_sup1 0).
  apply (@le_ereal_sup _ [set 0] IG).
  rewrite sub1set inE.
  exists (fun x => 0%E); last first.
    exact: integral0.
  split => //.
    exact : integrable0.
  move=> E.
  by rewrite integral0.
have finM : M < +oo.
  rewrite /M.
  move: IGbound.
  move=> [m] IGbound.
  apply : (@le_lt_trans _ _ m%:E); last by rewrite ltey.
  apply ub_ereal_sup.
  move=> x IGx.
  apply IGbound.
  by rewrite inE.
have finnumM : in_mem M (mem fin_num). (* M \is fin_num *)
  by rewrite ge0_fin_numE.
(*suff H1 : exists f : X -> \bar R, \int[mu]_x f x = M /\
                           forall E, E \in measurable -> (\int[mu]_(x in E) f x)%E = nu E.
  admit.*)
have [g H2] : exists g : (X -> \bar R)^nat, forall m, g m \in G /\ \int[mu]_x (g m x) >= M - m.+1%:R^-1%:E.
  pose P (m: nat) (g : X -> \bar R) := g \in G /\ M - (m.+1%:R^-1)%:E <= \int[mu]_x g x.
  suff : { g : (X -> \bar R) ^nat & forall m : nat, P m (g m)}.
    case => g Hg.
    by exists g.
  apply choice.
  move=> m.
  rewrite /P.
  have /(@ub_ereal_sup_adherent _ IG) : (0 < m.+1%:R^-1 :> R)%R by rewrite invr_gt0.
  move/(_ finnumM) => [_ [h Gh <-]].
  exists h; rewrite inE; split => //; rewrite -/M in q.
  exact/ltW.
pose F (m : nat) (x : X) := \big[maxe/-oo]_(j < m) (g j x).
(* have : forall m x, F m x >= 0
 *   forall x, 0 <= g m x, g m in G
 *)
 (* max_g2' : (T -> R)^nat :=
  fun k t => (\big[maxr/0]_(i < k) (g2' i k) t)%R. *)
have : forall n, measurable_fun setT (g n).
  move=> n.
  move: (H2 n).
  rewrite /G.
  by rewrite inE /= => -[[_ []]].
move=> mgn.
have mF n: measurable_fun setT (F n).
  induction n.
    rewrite /F.
    under eq_fun do rewrite big_ord0 ; rewrite -/(measurable_fun _ _).
    exact: measurable_fun_cst.
  rewrite /F.
  move=> m.
  under eq_fun do rewrite  big_ord_recr.
  apply : emeasurable_fun_max => //.
pose E m j := [set x | F m x = g j x /\ forall k, (k < j)%nat -> F m x > g k x ].

have H1 m j : E m j = [set x| F m x = g j x] `&` [set x |forall k, (k < j)%nat -> (g k x < g j x)%E].
  apply /seteqP.
  split; move=> x; rewrite /E /=; by case => ->.
have : (E 0%nat 0%nat) = setT.
  rewrite /E.
  rewrite /F.

have :forall m j, (j < m.+1)%nat -> E m.+1 j = (E m j) `\` (E m.+1 m.+1).

have partition_E n : partition setT (E n) setT.
  split => //.
      rewrite /E.
      admit.
    admit.
  admit.
  (* set の分解? *)
have measurable_E m j : E m j \in measurable.
  rewrite inE.
  rewrite H1.
  apply measurableI => /=.
  rewrite /E /=.
  rewrite H1.
  admit.
(* Local Open Scope ereal_scope. *)
have Fleqnu m E0 (mE : E0 \in measurable) : \int[mu]_(x in E0) F m x <= nu E0.
  have H'1 : \int[mu]_(x in E0) F m x = \sum_(j < m) \int[mu]_(x in (E0 `&` (E m j))) F m x.
    admit.
  have H'2 : \sum_(j < m) (\int[mu]_(x in (E0 `&` (E m j))) F m x) =
             \sum_(j < m) (\int[mu]_(x in (E0 `&` (E m j))) g m x).
    admit.
  have H'3 : \sum_(j < m) (\int[mu]_(x in (E0 `&` (E m j))) g m x) <=
             \sum_(j < m) nu (E0 `&` (E m j)).
    admit.
  have H'4 : \sum_(j < m) (nu (E0 `&` (E m j))) = nu E0.
    admit.
  by rewrite H'1 H'2 -H'4; exact H'3.
have FminG m : F m \in G.
    admit.
have Fgeqg m : forall x, F m x >= g m x.
  admit.
have nd_F m x : nondecreasing_seq (F ^~ x).
  admit.
pose limF := fun (x : X) => lim (F^~ x) : \bar R.
exists limF.
have mlimF : @measurable_fun _ _ X _ setT limF.
  admit.
have limF0 x : 0 <= limF x.
  rewrite /limF.
  apply ereal_lim_ge.
    apply ereal_nondecreasing_is_cvg.
    move=> n m.
    rewrite /F.
    move=> nm.
    by apply (bigmax_lee (fun n => g n x)).
 (* note: rename homo_le_bigmax *)
  near=> n.
  have n0 : (0 < n)%nat.
    near: n.
    by exists 1%nat.
  rewrite /F.
  destruct n => //.
  apply : (bigmax_sup ord_max) => //.
  have := H2 n.
  case.
  rewrite inE /G /=.
  by case.
have limFleqnu : forall E, \int[mu]_(x in E) limF x <= nu E.
  admit.
have limFXeqM : \int[mu]_x limF x = M.
  admit.
split.
- admit.
- admit.
- (* Reductio ad absurdum *)
  move=> E0 mE0.
  apply/eqP; rewrite eq_le limFleqnu andbT; apply/negP => abs.
  have [eps Heps] : exists eps : {posnum R}, \int[mu]_(x in E0) (limF x + eps%:num%:E) < nu E0.
    admit.
  have sigma : {smeasure set X -> \bar R}.
    admit.
  have sigmaE : forall F, sigma F = nu F - \int[mu]_(x in F) (limF x + eps%:num%:E).
    admit.
  move : (Hahn_decomposition sigma) => [P [N [posP negN PNX PN0]]].
pose E0P := E0 `&` P.
pose E0N := E0 `&` N.
move: (posP) => [mP _].
move: negN => [mN negN].
rewrite !inE in mE0 mP mN.
have mE0P : measurable E0P.
  apply measurableI => //.
have muE0P0: mu E0P > 0.
  rewrite /abs_continuous.
  rewrite lt_neqAle.
  rewrite measure_ge0.
  rewrite andbT.
  move : mudomnu.
  rewrite /abs_continuous.
  move=> /(_ E0P).
  move=> H.
  move: (H mE0P) => mu0nu0.
Check nu E0P = 0 .
  move: (contra_not_neq mu0nu0).
  move=> HH.
  rewrite eq_sym.
  apply HH.
  apply /eqP.
  rewrite gt_eqF //.
  have : sigma E0P > 0.
   apply (@lt_le_trans _ _ (sigma E0)) ; last first.
      rewrite (s_measure_partition2 _ mP mN PNX PN0) //.
      rewrite gee_addl //.
      apply negN => //.
      rewrite inE.
      apply measurableI => //.
    rewrite sigmaE.
    rewrite sube_gt0 //.
  rewrite sigmaE.
  rewrite sube_gt0.
  apply : le_lt_trans.
  apply integral_ge0.
  move=> x _.
  by rewrite adde_ge0.
pose h x := if (x \in E0P) then (limF x + (eps%:num)%:E) else (limF x).
have hnu : forall S, measurable S -> \int[mu]_(x in S) h x <= nu S.
  admit.
(* have posE0P : positive_set sigma E0P. *)
have : \int[mu]_(x in setT) h x > M.
  rewrite -(setUv E0P).
  rewrite integral_setU //; last 4 first.
          by apply measurableC.
        rewrite (setUv E0P).
        admit.
      admit.
    apply /disj_set2P.
    exact : setIv.
  rewrite /h.
  rewrite -(eq_integral _ (fun x => limF x + (eps%:num)%:E)); last first.
    move=> x xE0P.
    by rewrite ifT.
  rewrite -[\int[mu]_(x in ~` E0P) _](eq_integral _ (fun x => limF x)); last first.
    move=> x xnE0P.
    rewrite ifF //.
    apply negbTE.
    by rewrite -in_setC.
  rewrite ge0_integralD//; last 2 first.
      admit.
    exact : measurable_fun_cst.
  rewrite integral_cst //.
  rewrite addeAC.
  rewrite -integral_setU //; last 3 first. (* 上のintegral_setU以降と同じ *)
        admit.
      admit.
    admit.
  rewrite setUv.
  rewrite limFXeqM.
  rewrite -lte_subel_addl; last first.
    rewrite ge0_fin_numE //.
  rewrite subee //.
  apply mule_gt0 => //.
have hinG: G h.
  rewrite /G //=.
  split.
      admit. (* *)
    admit.
  move=> S.
  rewrite inE.
  apply : hnu.
have : (\int[mu]_x h x <= M).
  rewrite -(ereal_sup1 (\int[mu]_x h x)).
  apply (@le_ereal_sup _ [set \int[mu]_x h x] IG).
  rewrite sub1set inE.
  exists h => //.
rewrite leNgt.
apply /negP.
(*have hnuP: forall S, measurable S -> S `<=` P -> \int[mu]_(x in S) h x <= nu S.
  move=> S mS SP.
  admit.
have hnuN : forall S, measurable S -> S `<=` N -> \int[mu]_(x in S) h x <= nu S.
  admit.
*)
Admitted.

Theorem Radon_Nikodym d (X : measurableType d) (R : realType)
    (mu : {measure set X -> \bar R}) (nu : {smeasure set X -> \bar R})
    (musigmafinite : sigma_finite setT mu) :
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
x
