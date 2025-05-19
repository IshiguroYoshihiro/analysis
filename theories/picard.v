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
