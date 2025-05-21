(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval poly.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions reals interval_inference topology.
From mathcomp Require Import prodnormedzmodule tvs normedtype landau forms.
From mathcomp Require Import sequences derive measure lebesgue_measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral ftc.

(**md**************************************************************************)
(* # ODE                                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(*
HB.factory Record isNormedModule (K : realType) M
  of Num.NormedZmodule K M := {
}.
*)

Definition pseudometric (K : realType) (M : normedZmodType K) : Type := M.

HB.instance Definition _ (K : realType) (M : normedZmodType K) :=
  Choice.on (pseudometric M).
HB.instance Definition _ (K : realType) (M : normedZmodType K) :=
  Num.NormedZmodule.on (pseudometric M).
HB.instance Definition _ (K : realType) (M : normedZmodType K) :=
  isPointed.Build M 0.

(*HB.builders Context K M of isNormedModule K M.*)

Section isnormedmodule.
Variables (K : realType) (M' : normedZmodType K).

Notation M := (pseudometric M').

Local Definition ball (x : M) (r : K) : set M := ball_ Num.norm x r.

Local Definition ent : set_system (M * M) :=
  entourage_ ball.

Local Definition nbhs (x : M) : set_system M :=
  nbhs_ ent x.

Local Lemma nbhsE : nbhs = nbhs_ ent. Proof. by []. Qed.

HB.instance Definition _ := hasNbhs.Build M nbhs.

Local Lemma ball_center x (e : K) : 0 < e -> ball x e x.
Proof. by rewrite /ball/= subrr normr0. Qed.

Local Lemma ball_sym x y (e : K) : ball x e y -> ball y e x.
Proof. by rewrite /ball /= distrC. Qed.

Local Lemma ball_triangle x y z e1 e2 : ball x e1 y -> ball y e2 z ->
  ball x (e1 + e2) z.
Proof.
rewrite /ball /= => ? ?.
(*rewrite -[z](subrK y) -addrA. (le_lt_trans (ler_normD _ _))// addrC ltrD.*)
Admitted.

Local Lemma entourageE : ent = entourage_ ball.
Proof. by []. Qed.

HB.instance Definition _ := @Nbhs_isPseudoMetric.Build K M
  ent nbhsE ball ball_center ball_sym ball_triangle entourageE.

(*HB.end.*)

End isnormedmodule.

HB.mixin Record isContFun (R : realType) (a b : R)
    (f : {fun `[a, b] >-> [set: R]}) := {
  contFun : {in `[a, b], continuous f}
}.

#[short(type="contFunType")]
HB.structure Definition ContFun (R : realType) (a b : R) :=
  {f of isContFun R a b f}.

(* TODO: factory Lmodule is normed *)

HB.instance Definition _ (R : realType) (a b : R) :=
  gen_eqMixin (contFunType a b).
HB.instance Definition _ (R : realType) (a b : R) :=
  gen_choiceMixin (contFunType a b).

Section contFunType_isZmodule.
Context {R : realType} (a b : R).

Local Notation F := ({fun `[a, b] >-> [set: R]}).

Local Notation V := (contFunType a b).

Local Lemma set_fun0 : {homo cst 0 : x / `[a, b] x >-> [set: R] x}.
Proof. by []. Qed.

HB.instance Definition _ := @isFun.Build _ _ `[a, b] setT (cst 0) set_fun0.

Local Lemma contFun0 : {in `[a, b], continuous (@cst R R 0)}.
Proof. by move=> x _; exact: cst_continuous. Qed.

HB.instance Definition _ := @isContFun.Build R a b (@cst R R 0) contFun0.

Local Definition zero : V := (@cst R R 0 : F).

Definition opp' (f : F) : F := -%R \o f.

Local Lemma contFun_opp (f : V) : {in `[a, b], continuous (opp' f)}.
Proof. by move=> x xab; exact/continuousN/contFun. Qed.

HB.instance Definition _ (f : V) :=
  @isContFun.Build R a b (opp' f) (@contFun_opp f).

Local Lemma set_funD (f g : F) : {homo f \+ g : x / `[a, b] x >-> [set: R] x}.
Proof. by []. Qed.

HB.instance Definition _ (f g : F) :=
  @isFun.Build _ _ `[a, b] setT (f \+ g) (set_funD f g).

Definition add' (f g : F) : F := f \+ g.

Local Lemma contFun_add (f g : V) : {in `[a, b], continuous (add' f g)}.
Proof. by move=> x xab; apply/continuousD; exact/contFun. Qed.

HB.instance Definition _ (f g : V) :=
  @isContFun.Build R a b (add' f g) (@contFun_add f g).

Lemma contFunP : forall f g : V, f = g <-> f =1 g.
Admitted.

Local Lemma addrA : associative (fun f g : V => add' f g : V).
Proof.
move=> f g h.
apply/contFunP => /= x/=.
by rewrite addrA.
Qed.

Local Lemma addrC : commutative (fun f g : V => add' f g : V).
Proof.
move=> f g.
Admitted.

Local Lemma add0r : left_id zero (fun f g : V => add' f g).
Proof.
move=> x.
Admitted.

Local Lemma addNr : left_inverse zero (fun f : V => opp' f : V) (fun f g : V => add' f g).
Proof.
Admitted.

Fail Check V : zmodType.

HB.instance Definition _ := @GRing.isZmodule.Build V zero
  (fun f : V => opp' f : V) (fun f g : V => add' f g : V)
  addrA addrC add0r addNr.

Check V : zmodType.

End contFunType_isZmodule.

Section zmodule_normed.
Context {R : realType} (a b : R).

Definition infty_norm (f : {fun `[a, b] >-> [set: R]}) :=
  sup ((Num.norm \o f) @` `[a, b]).

Local Notation V := (contFunType a b).

Local Notation norm := infty_norm.

Local Lemma ler_normD x y : norm (add' x y) <= norm x + norm y :> R.
Proof.
Admitted.

Local Lemma normr0_eq0 (x : V) : norm x = 0 -> x = 0.
Admitted.

Local Lemma normrMn (x : V) n : norm (x *+ n) = norm x *+ n.
Admitted.

Local Lemma normrN (x : V) : norm (opp' x) = norm x.
Admitted.
(* TODO: dev the theory of sup following the theory of ess_sup *)

Fail Check V : normedZmodType R.

HB.instance Definition _ := @Num.Zmodule_isNormed.Build R V
  norm ler_normD normr0_eq0 normrMn normrN.

Check V : normedZmodType R.

Check (pseudometric V) : pseudoMetricType R.
Check (pseudometric V) : normedZmodType R.
Fail Check (pseudometric V) : normedModType R.

End zmodule_normed.

Fail HB.about Lmodule_isNormed.

HB.factory Record Lmodule_isNormed (R : realType) M
    of GRing.Lmodule R M := {
 norm : M -> R;
 ler_normD : forall x y, norm (x + y) <= norm x + norm y ;
(* normrMn : forall x n, norm (x *+ n) = norm x *+ n ;*)
 normrN : forall x, norm (- x) = norm x ;
 normrZ : forall (l : R) (x : M), norm (l *: x) = `|l| * norm x ;
 normr0_eq0 : forall x : M, norm x = 0 -> x = 0
}.

HB.builders Context R M of Lmodule_isNormed R M.

HB.about Num.Zmodule_isNormed.Build.

Lemma normrMn x n : norm (x *+ n) = norm x *+ n.
Admitted. (* from normrZ *)

HB.instance Definition _ := Num.Zmodule_isNormed.Build
  R M ler_normD normr0_eq0 normrMn normrN.

Check M : normedZmodType R.

Check (@pseudometric R M).

HB.saturate pseudometric.

Check (pseudometric M : pseudoMetricType R).

HB.instance Definition _ := PseudoMetric.copy M (pseudometric M).
HB.instance Definition _ := isPointed.Build M 0.

Lemma whatever : NormedZmod_PseudoMetric_eq R M.
Proof.
by constructor.
Qed.

HB.instance Definition _ := whatever.

Lemma coucou : PseudoMetricNormedZmod_Lmodule_isNormedModule R M.
Proof.
constructor.
exact: normrZ.
Qed.

HB.instance Definition _ := coucou.

Check M : normedModType R.

HB.end.

xxx

(* dy = f(t, y(t)), y(t0) = y0 *)
Record IVP (R : realType) := {
  time_domain : interval R ;
  open_time_domain : open [set` time_domain] ;
  value_domain : interval R ;
  rhs : R -> R -> R ;
  initial_time : R (* t0 *) ;
  initial_time_domain : initial_time \in time_domain ;
  initial_value : R (* y0 *) ;
  initial_value_domain : initial_value \in value_domain ;
}.

Section solution_of_an_IVP.
Context {R : realType}.
Variable pbm : @IVP R.

Let t0 := initial_time pbm.
Let y0 := initial_value pbm.
Let rhs := rhs pbm.

Definition solution (i : interval R) (y : R -> R) :=
  [/\ t0 \in i,
      open [set` i],
      y @` [set` time_domain pbm] `<=` [set` value_domain pbm],
      {in i, forall t, y^`() t = rhs t (y t)} &
      y t0 = y0 ].

Let i := time_domain pbm.
Let j := value_domain pbm.
Hypothesis rhs_cont : forall y, y \in j -> {in i, continuous (rhs ^~ y)}.
Hypothesis rhs_lip : forall x, x \in i -> [lipschitz rhs x y | y in [set: R]].

Let mu := @lebesgue_measure R.

Definition inte a b f :=
  if a < b then \int[mu]_(x in `[a, b]) f x else - \int[mu]_(x in `[b, a]) f x.

Reserved Notation "\int [ mu ]_( x $ a ~ b ) F"
  (at level 36, F at level 36, mu at level 10,
  format "'[' \int [ mu ]_( x $ a ~ b )  '/  '  F ']'").

Notation "\int [ mu ]_( x $ a ~ b ) f" :=
  (inte a b (fun x => f)).

Lemma picard : exists (i : interval R) (y : R -> R), solution i y.
Proof.
pose f (y : R -> R) (t : R) := y0 + \int[mu]_(x $ t0 ~ t) rhs x (y x).
have : is_contraction f.
