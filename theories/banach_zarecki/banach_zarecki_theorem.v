From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals constructive_ereal topology normedtype.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import absolute_continuity banach_zarecki_lemma6.
From mathcomp Require Import banach_zarecki_lemma7 banach_zarecki_lemma8.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem                                                   *)
(*                                                                            *)
(* ref: Vasile Ene, An Elementary Proof of the Banach–Zarecki Theorem,        *)
(* Real Analysis Exchange 23(1):295-301                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section banach_zarecki.
Context {R : realType}.
Variables a b : R.
Hypotheses ab : a < b.

Local Notation mu := (@completed_lebesgue_measure R).

Theorem Banach_Zarecki (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] f ->
  abs_cont a b f.
Proof.
move=> cf bvf Lf.
apply: total_variation_AC => //. (* lemma 8 *)
apply: Banach_Zarecki_nondecreasing => //. (* lemma 7 *)
- exact: total_variation_continuous.
- move=> x y; rewrite !in_itv /= => /andP[ax xb] /andP[ay yb] xy.
  apply: fine_le.
  + apply/(bounded_variationP _ ax); exact:(bounded_variationl _ xb).
  + apply/(bounded_variationP _ ay); exact:(bounded_variationl _ yb).
  + by apply: (@total_variation_nondecreasing _ _ b); rewrite ?in_itv /= ?ax ?ay.
- by apply: lemma6_direct_new.lemma6_direct => //.
Qed.

End banach_zarecki.
