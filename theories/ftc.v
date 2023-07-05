(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.classical Require Import cardinality fsbigop mathcomp_extra.
Require Import reals ereal signed topology numfun normedtype.
From HB Require Import structures.
Require Import sequences esum measure real_interval realfun.
Require Import lebesgue_measure lebesgue_integral charge.
Require Import derive.
Require Import lebesgue_stieltjes_measure.

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

Let e n : R := n.+1%:R ^-1.

Definition derivative f :=
  get (fun f' : R -> R => {ae mu, forall t, F f e ^~ t --> f' t}).

(*
Let NR := [normedModType R of R for [normedModType R of R^o]].

Lemma measurable_fun_derive f : continuous f -> measurable_fun setT (@derive _ NR NR f).
Proof.
*)

Lemma measurable_fun_derivative f :continuous f -> measurable_fun setT f
  -> measurable_fun setT (derivative f).
Proof.
move=> /= cont_f deriv_f.
(* measurable_fun_derivative *)
rewrite /derivative//=.
move=> _ /= S mS.
apply measurableI => //.
Admitted.

Theorem thm7211 f (a b : R) : 
  {homo f : x y / (x <= y)%R} (* f increasing over [a, b] *) ->
  mu.-integrable `[a, b] (EFin \o (derivative f)) /\
  \int[mu]_(x in `[a, b]) (derivative f x)%:E <= (f b - f a)%:E.
Proof.
move=> nd_f.
split.

  (* split. *)
  (*   apply (measurable_funS measurableT) => //. *)
  (*   apply: (@measurable_fun_comp _ _ _ _ _ _ setT) => //. *)
  (*   apply measurable_fun_derivative => //. *)
  (*   admit. *)
(*
  split.
    apply: (@measurable_fun_comp _ _ _ _ _ _ setT) => //.
    apply: subspace_continuous_measurable_fun => //.
      exact: measurable_itv.
    admit.
  admit. (* by fatou's lemma?! *)
(* split => //. *)
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
        apply(@measurable_fun_comp _ _ _ _ _ _ setT) => //.
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
*)
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
  ereal_sup [set x : \bar R | exists (n : nat) (p : R ^nat),
     p 0%nat = a /\ p n = b /\ (forall k, p k < p k.+1)
        /\ x = (\sum_(i < n) `| f (p i) - f (p i.+1) |)%:E].

(* bouded variation*)
Definition variation_lty f a b := ((variation f a b) < +oo)%O.

Lemma variation_nondecreasing a b f : variation_lty f a b ->
  {homo variation f a : x y / (x <= y)%O}.
Admitted.

Lemma variationB_nondecreasing a b f : variation_lty f a b ->
  {homo (fun x => (variation f a x - EFin(f x))%E) : x y / (x <= y)%O}.
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
  (mu nu : {charge set gitvs -> \bar R}):
    nu `<< mu <-> forall e, 0 < e -> exists d, 0 < d /\
      (forall S, (measurable S /\ mu S < d) -> nu S < e).
Proof.
move=> /=.
split.
  move=> nu_mu e e0.
Admitted.

Lemma abs_cont_bounded_variation
  (f : R -> R) (a b : R) :
    abs_continuous f a b -> variation_lty f a b.
Proof.
move=> absf.
move: (absf (PosNum lte01)) => /= [] [d1 /= d1ge0]  H.
rewrite /variation_lty.
pose n :=  (ceil ((b - a) / d1)).
(*
pose P k : (R * R) := (a + (b - a) / n%R * k%R,
                      a + (b - a) / n%R * k.+1%R).

apply:S(le_lt_trans ((variation f a b)%:E < n)).
*)

(* for all m partition Q,
 * consider about the common partition R := P n \/ Q.
 * then
      \sum_(i < m) `| f (Q i) - f (Q i.+1) |
   <= \sum_(i < n+m) `| f (R i) - f (R i.+1) |
   <= \sum_(i < n) \sum_(k < n+m | P i < R k <= P i.+1) `| f (R i) - f ( R i.+1)|
   < \sum_(i < n) 1 (by abs continuity)
   = n
 *)
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
