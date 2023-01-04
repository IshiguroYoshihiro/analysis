(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.classical Require Import cardinality fsbigop mathcomp_extra.
Require Import reals ereal signed topology numfun normedtype.
From HB Require Import structures.
Require Import sequences esum measure real_interval realfun.
Require Import lebesgue_measure lebesgue_integral smeasure radon_nikodym.
Require Import derive.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(* scratch file to sketch the FTC                                             *)
(******************************************************************************)

(* the following is the axiomatized version of
   https://github.com/math-comp/analysis/pull/677,
   waiting to be merged into master *)
Notation right_continuous f :=
  (forall x, f%function @ at_right x --> f%function x).

(*
Lemma right_continuousW (R : numFieldType) (f : R -> R) :
  continuous f -> right_continuous f.
Admitted.*)

HB.mixin Record isCumulative (R : numFieldType) (f : R -> R) := {
  cumulative_is_nondecreasing : {homo f : x y / x <= y} ;
  cumulative_is_right_continuous : right_continuous f }.

#[short(type=cumulative)]
HB.structure Definition Cumulative (R : numFieldType) :=
  { f of isCumulative R f }.

Arguments cumulative_is_nondecreasing {R} _.
Arguments cumulative_is_right_continuous {R} _.

(*Lemma nondecreasing_right_continuousP (R : numFieldType) (a : R) (e : R)
    (f : cumulative R) :
  e > 0 -> exists d : {posnum R}, f (a + d%:num) <= f a + e.
Admitted.

Section id_is_cumulative.
Variable R : realType.

Let id_nd : {homo @idfun R : x y / x <= y}.
Admitted.

Let id_rc : right_continuous (@idfun R).
Admitted.

HB.instance Definition _ := isCumulative.Build R idfun id_nd id_rc.
End id_is_cumulative.

(* TODO: move and use in lebesgue_measure.v? *)
Lemma le_inf (R : realType) (S1 S2 : set R) :
  -%R @` S2 `<=` down (-%R @` S1) -> nonempty S2 -> has_inf S1
    -> (inf S1 <= inf S2)%R.
Admitted.
*)

Definition EFinf {R : numDomainType} (f : R -> R) : \bar R -> \bar R :=
  fun x => if x is r%:E then (f r)%:E else x.

(*Lemma nondecreasing_EFinf (R : realDomainType) (f : R -> R) :
  {homo f : x y / (x <= y)%R} -> {homo EFinf f : x y / (x <= y)%E}.
Admitted.
*)
Section hlength.
Local Open Scope ereal_scope.
Variables (R : realType) (f : R -> R).
Let g : \bar R -> \bar R := EFinf f.

Implicit Types i j : interval R.
Definition itvs : Type := R.

Definition hlength (A : set itvs) : \bar R := let i := Rhull A in g i.2 - g i.1.

(*Lemma hlength0 : hlength (set0 : set R) = 0.
Admitted.

Lemma hlength_singleton (r : R) : hlength `[r, r] = 0.
Proof.
Admitted.

Lemma hlength_itv i : hlength [set` i] = if i.2 > i.1 then g i.2 - g i.1 else 0.
Admitted.

Lemma hlength_setT : hlength setT = +oo%E :> \bar R.
Admitted.

Lemma hlength_finite_fin_num i : neitv i -> hlength [set` i] < +oo ->
  ((i.1 : \bar R) \is a fin_num) /\ ((i.2 : \bar R) \is a fin_num).
Admitted.

Lemma finite_hlengthE i : neitv i -> hlength [set` i] < +oo ->
  hlength [set` i] = (fine (g i.2))%:E - (fine (g i.1))%:E.
Admitted.

Lemma hlength_itv_bnd (a b : R) (x y : bool): (a <= b)%R ->
  hlength [set` Interval (BSide x a) (BSide y b)] = (f b - f a)%:E.
Admitted.

Lemma hlength_infty_bnd b r :
  hlength [set` Interval -oo%O (BSide b r)] = +oo :> \bar R.
Admitted.

Lemma hlength_bnd_infty b r :
  hlength [set` Interval (BSide b r) +oo%O] = +oo :> \bar R.
Admitted.

Lemma pinfty_hlength i : hlength [set` i] = +oo ->
  (exists s r, i = Interval -oo%O (BSide s r) \/ i = Interval (BSide s r) +oo%O)
  \/ i = `]-oo, +oo[.
Admitted.

Lemma hlength_ge0 (ndf : {homo f : x y / (x <= y)%R}) i : 0 <= hlength [set` i].
Admitted.

Local Hint Extern 0 (0%:E <= hlength _) => solve[apply: hlength_ge0] : core.

Lemma hlength_Rhull (A : set R) : hlength [set` Rhull A] = hlength A.
Admitted.

Lemma le_hlength_itv (ndf : {homo f : x y / (x <= y)%R}) i j :
  {subset i <= j} -> hlength [set` i] <= hlength [set` j].
Admitted.

Lemma le_hlength (ndf : {homo f : x y / (x <= y)%R}) :
  {homo hlength : A B / A `<=` B >-> A <= B}.
Admitted.
*)
End hlength.
Arguments hlength {R}.
(*#[global] Hint Extern 0 (0%:E <= hlength _) => solve[apply: hlength_ge0] : core.

Section itv_semiRingOfSets.
Variable R : realType.
Implicit Types (I J K : set R).
Definition ocitv_type : Type := R.

Definition ocitv := [set `]x.1, x.2]%classic | x in [set: R * R]].

Lemma is_ocitv a b : ocitv `]a, b]%classic.
Admitted.
Hint Extern 0 (ocitv _) => solve [apply: is_ocitv] : core.

Lemma ocitv0 : ocitv set0.
Admitted.
Hint Resolve ocitv0 : core.

Lemma ocitvP X :
  ocitv X <-> X = set0 \/ exists2 x, x.1 < x.2 & X = `]x.1, x.2]%classic.
Admitted.

Lemma ocitvD : semi_setD_closed ocitv.
Admitted.

Lemma ocitvI : setI_closed ocitv.
Admitted.

Variable d : measure_display.

HB.instance Definition _ := @isSemiRingOfSets.Build d ocitv_type
  (Pointed.class R) ocitv ocitv0 ocitvI ocitvD.

Definition itvs_semiRingOfSets := [the semiRingOfSetsType d of ocitv_type].

Lemma hlength_semi_additive (f : R -> R) :
  semi_additive (hlength f : set ocitv_type -> _).
Admitted.

Hint Extern 0 (measurable _) => solve [apply: is_ocitv] : core.

Lemma hlength_sigma_finite (f : R -> R) :
  sigma_finite [set: ocitv_type] (hlength f).
Admitted.

Lemma hlength_ge0' (f : cumulative R) (I : set ocitv_type) :
  measurable I -> (0 <= hlength f I)%E.
Admitted.

HB.instance Definition _ (f : cumulative R) :=
  isAdditiveMeasure.Build _ R _ (hlength f : set ocitv_type -> _)
    (hlength_ge0' f) (hlength_semi_additive f).

Lemma hlength_content_sub_fsum (f : cumulative R) (D : {fset nat}) a0 b0
    (a b : nat -> R) : (forall i, i \in D -> a i <= b i) ->
    `]a0, b0] `<=` \big[setU/set0]_(i <- D) `] a i, b i]%classic ->
  f b0 - f a0 <= \sum_(i <- D) (f (b i) - f (a i)).
Admitted.

Lemma hlength_sigma_sub_additive (f : cumulative R) :
  sigma_sub_additive (hlength f : set ocitv_type -> _).
Admitted.

Let gitvs := [the measurableType _ of salgebraType ocitv].

Definition lebesgue_stieltjes_measure (f : cumulative R) :=
  Hahn_ext [the additive_measure _ _ of hlength f : set ocitv_type -> _ ].

End itv_semiRingOfSets.
Arguments lebesgue_stieltjes_measure {R}.

Section lebesgue_stieltjes_measure_itv.
Variables (d : measure_display) (R : realType) (f : cumulative R).

Let m := lebesgue_stieltjes_measure d f.

Let g : \bar R -> \bar R := EFinf f.

Let lebesgue_stieltjes_measure_itvoc (a b : R) :
  (m `]a, b] = hlength f `]a, b])%classic.
Admitted.

End lebesgue_stieltjes_measure_itv.

Example lebesgue_measure d (R : realType)
    : set [the measurableType (d.-measurable).-sigma of salgebraType (d.-measurable)] -> \bar R :=
  lebesgue_stieltjes_measure _ [the cumulative _ of @idfun R].

(* /rnd Stieltjes *)

*)

(* reference:
   A Course in Functional Analysis and Measure Theory
   7.2
*)

Section newton_leibniz.
Local Open Scope ereal_scope.
Context (R : realType).
Let mu := @lebesgue_measure R.
Implicit Types f : R -> R.

Let F f (e : R ^nat) n t := ((f (t + e n) - f t) / e n)%R.

Let e n : R := n.+1%:R^-1.

Definition derivative f :=
  get (fun f' : R -> R => {ae mu, forall t, F f e ^~ t --> f' t}).

Theorem thm7211 f (a b : R) :
  {homo f : x y / (x <= y)%R} (* f increasing over [a, b] *) ->
  mu.-integrable `[a, b] (EFin \o (derivative f)) /\
  \int[mu]_(x in `[a, b]) (derivative f x)%:E <= (f b - f a)%:E.
Proof.
move=> nd_f.
have H2 : mu.-integrable `[a, b] (EFin \o derivative f).
  split.
    apply: measurable_fun_comp => //.
    apply: subspace_continuous_measurable_fun => //.
      exact: measurable_itv.
    admit.
  admit. (* by fatou's lemma?! *)
split => //.
pose f_ := F f e.
have me n : measurable_fun `[a, b] (fun=> e n).
  rewrite /e.
  apply: (measurable_funS measurableT) => //=.
  admit.
have H1 n : \int[mu]_(x in `[a, b]) (f_ n x)%:E <= (f b - f a)%:E.
  admit.
apply: (@le_trans _ _ (lim_einf (fun n => \int[mu]_(x in `[a, b]) (f_ n x)%:E))).
  apply: (@le_trans _ _ (\int[mu]_(x in `[a, b]) lim_einf (fun n => (f_ n x)%:E))).
    rewrite /f_.
    admit. (* by definition *)
  apply: fatou => //.
  - exact: measurable_itv.
  - move=> n .
    apply/EFin_measurable_fun.
    rewrite /f_ /F.
    apply/measurable_funM.
      apply/measurable_funB.
        apply/measurable_fun_comp => //.
          admit. (* by hypo? *)
        apply: measurable_funD.
          exact: measurable_fun_id.
        exact: me.
      admit. (* by hypo? *)
    admit.
  - move=> n x abx.
    rewrite lee_fin /f_ /F.
    apply/divr_ge0 => //.
      by rewrite subr_ge0 nd_f// ler_addl invr_ge0.
    by rewrite invr_ge0.
- rewrite is_cvg_lim_einfE; last first.
    admit.
  apply: lime_le.
    admit.
  exact: nearW.
Admitted.

End newton_leibniz.

Section primitive_function.
Local Open Scope ereal_scope.
Context (R : realType).
Let mu := [the measure _ _ of @lebesgue_measure R].

Definition primitive (f : R -> R) a x :=
  \int[mu]_(t in `[a, x]) (f t)%:E.

Theorem thm7221 (f : R -> R) (a b : R) :
  mu.-integrable `[a, b] (EFin \o f) ->
  {within `[a, b], continuous (primitive f a)}.
Proof.
Admitted.

Lemma lem7221 (f : R -> R) (a b : R) :
  (* primitive differentiable almost everywhere? *)
  mu.-integrable `[a, b] (EFin \o (derivative (fine \o primitive f a))) /\
  \int[mu]_(t in `[a, b]) `|(derivative (fine \o primitive f a) t)%:E| <=
  \int[mu]_(t in `[a, b]) `|f t|%:E.
Proof.
Admitted.

Theorem them7222 (f : R -> R) (a b : R) :
  mu.-integrable `[a, b] (EFin \o f) ->
  {ae mu, forall x, derivative (fine \o primitive f a) x = f x}.
Proof.
Admitted.

End primitive_function.

Reserved Notation "{ 'within' A , 'right_continuous' f }"
  (at level 70, A at level 69, format "{ 'within'  A ,  'right_continuous'  f }").
Notation "{ 'within' A , 'right_continuous' f }" := (forall x,
  cvg_to [filter of fmap f (filter_of (Phantom (subspace A) (at_right x)))]
         [filter of f x]).

Section variation.
Variable R : realType.

Definition variation (f : R -> R) (a b : R) :=
  sup [set x : R | exists (n : nat) (p : R ^nat),
     p 0%nat = a /\ p n = b /\ (forall k, p k < p k.+1)
        /\ x = \sum_(i < n) `| f (p i) - f (p i.+1) |].

(* bouded variation*)
Definition variation_lty f a b := ((variation f a b)%:E < +oo)%E.

Lemma variation_nondecreasing a b f : variation_lty f a b ->
  {homo variation f a : x y / x <= y}.
Admitted.

Lemma variationB_nondecreasing a b f : variation_lty f a b ->
  {homo variation f a \- f : x y / x <= y}.
Admitted.

Fail Lemma right_continuous_variation a b (f : R -> R) :
  right_continuous f -> variation_lty f a b ->
    {within `[a, b], right_continuous (variation f a)}.

Fail Lemma right_continuous_variationB a b f :
  right_continuous f -> variation_lty f a b ->
    {within `[a, b], right_continuous (variation f a \- f)}.

End variation.

(* maybe rewrite I : R * R to I : interval R *)
Definition abs_continuous (R : realType) (f : R -> R) a b :=
  forall e : {posnum R}, exists d : {posnum R},
    forall J : nat -> R * R, forall n : nat,
      \sum_(k < n)((J k).2 - (J k).1) < d%:num ->
        trivIset setT (fun n => `[(J n).1, (J n).2]%classic) ->
          (forall n, a <= (J n).1 /\ (J n).2 <= b) ->
            \sum_(k < n) `| f (J k).2 - f (J k).1 | < e%:num.

Section abs_cont_properties.
Local Open Scope ereal_scope.
Context (R : realType).
Let gitvs := [the measurableType _ of salgebraType (@ocitv R)].

Lemma dominatesE
  (mu nu : {smeasure set gitvs -> \bar R}):
    nu `<< mu <-> forall e, 0 < e -> exists d, 0 < d /\
      (forall S, (measurable S /\ mu S < d) -> nu S < e).
Proof.
move=> /=.
split.
  move=> nu_mu e e0.
Admitted.

End abs_cont_properties.

Definition lebesgue_stieltjes_measure (R : realType) (f : cumulative R) :
  {measure set [the measurableType _ of salgebraType (@ocitv R)] -> \bar R}.
Admitted.

Lemma abs_cont_equiv (R : realType) (f : cumulative R) a b :
  abs_continuous f a b
  <->
  mrestr (lebesgue_stieltjes_measure f) (measurable_itv `[a, b]) `<<
  mrestr (@lebesgue_measure R) (measurable_itv `[a, b]).
Proof.
Admitted.

(*

by Radon Nikodym:

exists f, Stieltjes_F[a, b] = \int[Lebesgue]_(x in [a,b]) f x = F b - F a

*)

Section ftc.

Theorem FTC2_direct (R : realType) (f : R -> R) (a b : R)
    (f_abscont : abs_continuous f a b) :
  let lambda := @lebesgue_measure R in
  exists f' : R -> \bar R, [/\
    lambda.-integrable `[a, b] f',
     {ae lambda, forall x, x \in `[a, b] -> f' x \is a fin_num} &
     forall x, x \in `[a, b] ->
      (f x - f a)%:E = (\int[lambda]_(x in `[a, x]) f' x)%E].
Proof.
Abort.

Theorem FTC2_converse (R : realType) (f : R -> R) (a b : R) :
  let lambda := @lebesgue_measure R in
  lambda.-integrable `[a, b] (EFin \o f) ->
  exists F,
    EFin \o F = primitive F a /\
    abs_continuous F a b /\
    {ae lambda, forall x, derivative F x = f x}.
Proof.
Abort.
