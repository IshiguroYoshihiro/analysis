From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals constructive_ereal topology normedtype.
From mathcomp Require Import measure lebesgue_measure realfun.
From mathcomp Require Import absolute_continuity.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 1)                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section lemma1.
Context {R : Type}.

(* Lemma not_subset01P (X : set R) (Y : set R) (f : {fun X >-> Y}) : *)
(*   not_subset01 f -> *)
(*   (exists x0 x1, *)
(*    [/\ x0 \in (Y `&` [set y | (X `&` f @^-1` [set y])]), *)
(*       x1 \in (Y `&` [set y | (X `&` f @^-1` [set y])]) & *)
(*       x0 != x1]). *)

Lemma lemma1 (X : set R) (Y : set R) (f : R -> R) (I : pointedType)
    (X_ : I -> set R) :
    {homo f : x / X x >-> Y x} ->
    (forall i, X_ i `<=` X) ->
  (\bigcap_i (f @` X_ i)) `\` preimages_gt1 X Y f `<=` f @` (\bigcap_i X_ i) /\
  f @` (\bigcap_i X_ i) `<=` \bigcap_i (f @` X_ i).
Proof.
move=> fXY X_x; split; last first.
  (* TODO: lemma? *)
  move=> _/= [x fX_x] <- i _; exists x => //.
  exact: fX_x.
move=> y [bigcap_y fy01].
have Yy : Y y.
  have [x X_pointx <-] := bigcap_y point Logic.I.
  by apply: fXY; apply: X_x; exact: X_pointx.
have [x [Xx yfx x_unique]] :
    exists x, [/\ X x, y = f x & forall x', X x' -> y = f x' -> x' = x].
  move/not_andP : fy01=> [//|(*\not_andP[|]*)].
  (* - move=> /set0P/negP/negPn/eqP fy0. *)
  (*   have [x X_pointx fxy] := bigcap_y point Logic.I. *)
  (*   exfalso. *)
  (*   move: fy0 => /eqP/negPn/negP; apply. *)
  (*   apply/set0P; exists x; split => //. *)
  (*   apply: X_x. *)
  (*   exact: X_pointx. *)
  move=> /contrapT y_unique.
  have [x Xx fxy] := bigcap_y (@point I) Logic.I.
  exists x; split=> //[| x' Xx' fxfx'].
    exact: (X_x point).
  apply: y_unique => //=; split => //.
  exact: (X_x point).
have X_f i : exists xi, X_ i xi /\ f xi = y.
  have [xi X_ixi <-] : (f @` X_ i) y by exact: bigcap_y.
  by exists xi.
exists x => // i _.
have [xi [X_ixi fxiy]] := X_f i.
have Xxi : X xi by apply: X_x; exact: X_ixi.
by rewrite -(x_unique _ Xxi (esym fxiy)).
Qed.

End lemma1.
