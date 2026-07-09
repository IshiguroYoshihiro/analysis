From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals constructive_ereal topology normedtype.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import absolute_continuity.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 8)                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* lemma8 *)
Lemma total_variation_AC {R : realType} a b (f : R -> R) : a < b ->
  bounded_variation a b f ->
  abs_cont a b (fine \o (total_variation a ^~ f)) -> abs_cont a b f.
Proof.
move=> ab BVf + e => /(_ e)[d ACf].
exists d => n B HB; have {ACf} := ACf n B HB.
move: HB => [B12Bab] tB sumBd sumfBe.
rewrite (le_lt_trans _ sumfBe)//; apply: ler_sum => /= i _.
have [B12 Bab] := B12Bab i (ltn_ord i).
have aBi1 : a <= (B i).1.
  apply: (incl_itv_lb_nat (n := n)) => // j jn.
  by have [] := B12Bab _ jn.
  have [_] := B12Bab _ jn.
  exact.
have Bi2b : (B i).2 <= b.
  apply: (incl_itv_ub_nat (n := n)) => // j jn.
  by have [] := B12Bab _ jn.
  have [_] := B12Bab _ jn.
  exact.
rewrite (le_trans (ler_norm (f (B i).2 - f (B i).1)))//=.
rewrite (total_variationD f aBi1 (ltW B12)) fineD.
  apply/(bounded_variationP f aBi1)/(@bounded_variationl _ _ _ b) => //.
  by rewrite (le_trans _ Bi2b)// ltW.
  apply/(bounded_variationP f (ltW B12)).
  apply/(bounded_variationl (ltW B12) Bi2b).
  by apply: (bounded_variationr aBi1) => //; rewrite (le_trans _ Bi2b)// ltW.
rewrite addrAC subrr add0r -subr_ge0 -lee_fin EFinB fineK.
  apply/(bounded_variationP f (ltW B12)).
  apply/(bounded_variationl (ltW B12) Bi2b).
  by apply/(bounded_variationr aBi1 _ BVf); rewrite (le_trans _ Bi2b)// ltW.
by rewrite leeBrDr// add0e total_variation_ge// ltW.
Qed.
