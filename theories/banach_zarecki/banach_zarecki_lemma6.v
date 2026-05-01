From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_boot all_order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean perm finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals constructive_ereal topology normedtype.
From mathcomp Require Import ereal sequences.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import absolute_continuity banach_zarecki_lemma2.
From mathcomp Require Import banach_zarecki_lemma3 banach_zarecki_lemma5.
From mathcomp Require Import banach_zarecki_lemma4 (* for contiguous intervals *).

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 6)                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

From mathcomp Require Import cardinality.
Section lemmas.
Context {R : realType}.
Local Notation mu := (@completed_lebesgue_measure R).

Lemma is_subset1_countable (A : set R) : is_subset1 A -> countable A.
Proof.
move=> A1.
have[->|] := eqVneq A set0.
  done.
move/set0P/is_subset1_set1/(_ A1) ->.
exact: countable1.
Qed.

Lemma omega_max0 (a b : R) f : omega_max a b f [:: b] = oscillation f `[a, b].
Proof. by rewrite/omega_max/= big_nat1. Qed.

Lemma nondecreasing_total_variation (a b : R) (f : R -> R) :
bounded_variation a b f ->
let H := fun x => fine (total_variation a ^~ f x) in
 {in `[a, b] &, nondecreasing_fun H}.
Proof.
move=> bvf H x y xab yab xy.
have axyf := @total_variation_nondecreasing R a b f _ _ xab yab xy.
rewrite /H fine_le//.
- apply/bounded_variationP => //.
    by move: xab; rewrite in_itv/= => /andP[].
  move: xab; rewrite in_itv/= => /andP[? ?].
by move: bvf; apply: bounded_variationl.
- apply/bounded_variationP => //.
    by move: yab; rewrite in_itv/= => /andP[].
  move: yab; rewrite in_itv/= => /andP[? ?].
  by move: bvf; apply: bounded_variationl.
Qed.

Lemma mesh_mem_filter (a b c d : R) (s : seq R) :
  a <= c -> d <= b ->
  mesh c d [seq x <- s | x \in `[c, d]] <= mesh a b s.
Proof.
Abort.

Lemma mesh_filter (a b : R) (s : seq R) (P : pred R) :
  mesh a b [seq x <- s | P x] <= mesh a b s.
Proof.
Abort.

End lemmas.

Section preliminaries.
Context {R : realType}.

Lemma nth_map_iota (x : R) (n : nat) (f : nat -> R) (i : nat) :
  (i < n)%N ->
  nth x [seq f k | k <- iota 0 n] i = f i.
Proof.
by move=> iltn; rewrite (nth_map 0%N) ?nth_iota; last by rewrite size_iota.
Qed.

Lemma nth_cons_map_iota (x y : R) (n : nat) (f : nat -> R) (i : nat) :
  (i < n.+1)%N ->
  nth x (y :: [seq f k | k <- iota 0 n]) i = if i == 0 then y else f i.
Proof.
Abort.

Definition lambda_partition (a b : R) (lambda : R) :=
  let n := (truncn ((b - a) / lambda)).+1 in
  [seq (a + (b - a) * i.+1%:R / n%:R) | i <- iota 0 n].

Local Notation lp := lambda_partition.

Lemma lambda_partition_size0_tmp (a b l : R) :
  (0 < (truncn ((b - a) / l)).+1)%N.
Proof. by []. Qed.

Lemma lambda_partition_size0 (a b l : R) :
  a < b -> 0 < l ->
  (0 < size (lp a b l))%N.
Proof.
move=> ab l0; by rewrite size_map size_iota lambda_partition_size0_tmp.
Qed.

Lemma lambda_partition_div_width (a b l : R) (i : nat) :
  a < b -> 0 < l ->
  `|nth b (a :: (lp a b l)) i.+1 - nth b (a :: (lp a b l)) i| < l.
Proof.
move=> ab l0.
have lpw0 := lambda_partition_size0_tmp.
case: i.
  rewrite /= mulr1 -addrA subrKC.
  rewrite gtr0_norm; last by rewrite divr_gt0// subr_gt0.
  rewrite ltr_pdivrMr// mulrC -ltr_pdivrMr//.
  exact: truncnS_gt.
move=> n.
have [|] := leqP n (truncn ((b - a) / l)).
  rewrite leq_eqVlt => /predU1P[-> |].
    rewrite nth_default; last by rewrite /= size_map size_iota.
    rewrite [lp a b l]lock /=; unlock; rewrite nth_map_iota//.
    by rewrite -mulrA divff// mulr1 subrKC subrr normr0.
  admit.
move=> nsize.
rewrite 2?nth_default ?subrr ?normr0//.
Abort.

Lemma lambda_partition_partition (a b l : R) :
  a < b -> 0 < l ->
  itv_partition a b (lp a b l).
Proof.
move=> ab l0.
split; last first.
- rewrite (last_nth b).
  rewrite -(@prednK (size _))/=; last exact: lambda_partition_size0.
  rewrite nth_map_iota//.
  rewrite size_map size_iota mulfK; first by rewrite subrKC.
  rewrite lt0r_neq0//.
- admit.
Abort.

Lemma lambda_mesh (a b l : R) :
  a < b -> 0 < l ->
  mesh a b (lp a b l) < l.
Proof.
move=> ab l0.
rewrite /mesh -bigmaxr_morph.
apply: bigmax_lt => // n _.
(*exact: lambda_partition_div_width.*)
Abort.

End preliminaries.

Section limit_point_closed.
Context {R : realType}.

Lemma not_limit_point_set1 (A : set R) (a : R) : ~ limit_point A a ->
  exists e : {posnum R}, ball a e%:num `&` A `<=` [set a].
Proof.
move=> Ua; apply/not_existsP => aAa.
apply: Ua; rewrite /limit_point => /= V [e /= e0 aeV].
have /nonsubset[/= x [[aex Ax] /eqP xa]] := aAa (PosNum e0).
by exists x; split => //; exact: aeV.
Qed.

Lemma limit_point_closed (A : set R) : closed (limit_point A).
Proof.
rewrite -openC.
set U : set R := ~` _.
rewrite openE/= => a /not_limit_point_set1[e AeAa].
rewrite /interior /nbhs/= /nbhs_ball_; exists e%:num => //= b bae.
suff : b \notin limit_point A by rewrite notin_setE.
have [{}bae aeEa] : nbhs b (ball a e%:num) /\ ball a e%:num `&` A `<=` [set a].
  have [ab|ab] := eqVneq a b.
    split=> [|/= r [aer Ar]].
      by rewrite ab; exact: nbhsx_ballx.
    exact: AeAa.
  split => //.
  rewrite /nbhs/= /nbhs_ball_/=.
  exists (Num.min `|b - a| (e%:num - `|b - a|)) => //=.
    by rewrite lt_min/= normr_gt0 subr_eq0 eq_sym ab/= subr_gt0 distrC.
  move=> x.
  rewrite /ball /ball_ /= lt_min => /andP[bxba bxe].
  by rewrite -(subrKA b) (le_lt_trans (ler_normD _ _))// -ltrBrDl (distrC a).
rewrite notin_setE => /limit_point_infinite_setP/(_ _ bae); apply.
exact: (sub_finite_set aeEa).
Qed.

Section checking.

Lemma isolated_id_set1 (x : R) : isolated [set x] = [set x].
Proof.
rewrite eqEsubset; split; first exact: isolatedS.
rewrite -[isolated _]setU0.
apply: (subset_trans (@subset_closure _ _)).
rewrite closure_isolated_limit_point.
apply: setUS.
move=> z.
move/limit_pointP => [z_ [zx nzx cvgz]]/=.
have := zx z.
have rzx : range z_ x by exists 0 => //; apply: zx.
apply/not_implyP; split => //.
Abort.

Lemma isolated_points_of_limit_points_is_not_empty :
  exists A : set R, isolated (limit_point A) !=set0.
Proof.
exists [set n.+1%:R^-1 | n in [set: nat]].
exists 0%:R; split.
  rewrite inE.
  apply/limit_pointP.
  exists (fun n => n.+1%:R^-1); split.
  - done.
  - move=> n.
    by rewrite lt0r_neq0.
  - have <- : inf [set n.+1%:R^-1 | n in [set: nat]] = 0%:R :> R.
      apply/eqP; rewrite eq_le; apply/andP; split; last first.
        apply: lb_le_inf.
          by exists 1; exists 0 => //; rewrite invr1.
        by move=> _ [n _ <-]; rewrite invr_ge0.
      rewrite -lee_fin.
      rewrite -ereal_inf_EFin; last 2 first.
      - by exists 0 => _ [n _ <-]; rewrite invr_ge0.
      - by exists 1; exists 0 => //; rewrite invr1.
      admit.
    apply: nonincreasing_cvgn.
      apply/nonincreasing_seqP => n.
      by rewrite lef_pV2 ?posrE// ler_nat.
    by exists 0%:R => _ [n _ <-]; rewrite invr_ge0 (_ : 0 = 0%:R)// ler_nat.
exists (ball 0 1).
  exact: nbhsx_ballx.
rewrite eqEsubset; split.
  move=> x/= [] _ l2.
  apply/not_notP => /eqP.
  rewrite eq_le.
  rewrite negb_and => /orP.
  rewrite -2!ltNge => -[]x0;move/limit_point_infinite_setP : l2; apply/existsNP.
    have [x1|x1] := leP 1 x.
      exists (ball x (x - 1 / 2)).
      apply/not_implyP; split.
        apply: nbhsx_ballx.
        rewrite subr_gt0.
        apply: lt_le_trans _ x1.
        rewrite div1r invf_lt1//.
        by rewrite (_ : 1 = 1%:R)// ltr_nat.
      rewrite not_notP.
      apply/finite_set_leP.
      exists 1.
      rewrite -(card_le_eqr (@card_set1 R 1%:R)).
      apply: subset_card_le.
      move=> r/= [+ [n _]];  move/[swap] => <-{r}.
      apply: contraPP.
      case: n => // n _.
(*
      apply/negP; rewrite /ball/= -leNgt.
      rewrite ler_normr; apply/orP; left.
      rewrite lerB//.
      rewrite ler_pdivlMr//.
      rewrite exprSr divfK//.
      apply: exprn_ile1 => //.
      rewrite invf_le1//.
      by rewrite (_ : 1 = 1%:R)// ler_nat.
    exists (ball x (x / 2)).
    apply/not_implyP; split.
      apply: nbhsx_ballx.
      by rewrite divr_gt0.
    rewrite not_notE.
    apply/finite_set_leP.
    exists (truncn (x / 2)).+1.
    apply: (@card_le_trans _ _ _
           [set n%:R | n in `I_((Nat.log2 (truncn (x / 2))).+1)]).
      apply: subset_card_le.
      move=> r/=[+ [n _]] => /[swap] => <-{r}.
      rewrite /ball/=.
      move/ltr_normlW; rewrite ltrBlDr -ltrBlDl {1}(splitr x) addrK => x2n.
      exists (Nat.log2 (truncn (x / 2))) => //.
      rewrite 
      rewrite -{2}(invrK 2) -{2}(expr1 2^-1).
      
      rewrite gtr0_norm; last first.
        rewrite 
  move/limit_pointP => [a_ [a2]].
rewrite subset_set1.
Lemma perfect_set_closedDisolated (A : set R) : closed A ->
  perfect_set (A `\` isolated A).
Proof.
move=> cA.
split.
*)
Abort.

End checking.

End limit_point_closed.
Arguments limit_point_closed {R} A.

(* TODO: PR *)
Section interior_lemmas.
Context {R : realType}.

Lemma isolated_interior_set0 (A : set R) :
  isolated (interior A) = set0.
Proof.
apply/eqP.
apply: contrapT.
move/negP.
move/set0P.
move=> [/= x [Ax /=[V]]].
rewrite nbhsE/=.
move=> [U [oU Ux] UV] => VAx.
have {V UV VAx}UAx : U `&` (interior A) = [set x].
  rewrite eqEsubset; split.
    rewrite -VAx.
    exact: setSI.
  rewrite sub1set inE; split => //.
  by rewrite inE in Ax.
have : open (U `&` (interior A)).
  apply: openI => //.
  exact: open_interior.
rewrite UAx.
move/(interior_id _).1.
rewrite interior_set1.
by rewrite eqEsubset => -[_ /(_ x erefl)].
Qed.

Lemma nonempty_open_interval_not_subset1 (A : set R) :
  A !=set0 -> open A -> is_interval A ->
  ~ is_subset1 A.
Proof.
move=> [x Ax] oA itvA.
apply/existsNP.
have /(_ x Ax)[e/= e0] := open_subball oA.
have e20 : 0 < e / 2 by exact: divr_gt0.
move/(_ (e / 2)).
have ballee2 : ball_ [eta normr] 0 e (e / 2).
  rewrite /ball_/= sub0r normrN gtr0_norm//.
by rewrite -subr_gt0 {1}(splitr e) addrK.
move/(_ ballee2 e20).
move/(subset_trans (subset_closure_half e20)).
Abort.

Lemma limit_point_interior (A : set R) :
  interior A `<=` limit_point (interior A).
Proof.
move=> /= x [e /=e0].
rewrite open_subsetE; last exact: ball_open.
 move=> ballxA.
apply/limit_pointP.
exists (fun n => x - e / n.+2%:R); split.
- move=> _/= [n _ <-].
  apply: ballxA; rewrite /ball_/=.
  rewrite opprB addrCA subrr addr0 ger0_norm; last first.
    by rewrite divr_ge0// ltW.
  rewrite ltr_pdivrMr//.
  rewrite ltr_pMr//.
  by rewrite {1}(_ : 1 = 1%:R)// ltr_nat.
- move=> n.
  rewrite neq_lt; apply/orP; left.
  rewrite gtrBl.
  by rewrite divr_gt0.
- rewrite -{2}(subr0 x).
  apply: cvgB.
    exact: cvg_cst.
  rewrite -(mulr0 e).
  apply: cvgM.
    exact: cvg_cst.
  apply/cvgrVy.
    by apply: nearW.
  under eq_cvg do rewrite /unstable.inv_fun/= invrK.
  apply/cvgrnyP.
  rewrite cvg_shiftS.
  rewrite (cvg_shiftS (fun x => x)).
  exact: cvg_id.
Qed.

Lemma ex_perfect_set (A : set R) :
  closed A ->
  exists B, [/\ B `<=` A, perfect_set B &
   (0 < lebesgue_measure A)%E -> (0 < lebesgue_measure B)%E].
Proof.
move=> cA.
exists (closure (interior A)); split.
- rewrite {2}((closure_id _).1 cA).
  apply: closureS.
  exact: interior_subset.
- apply/perfectP; split; first exact: closed_closure.
  rewrite closure_isolated_limit_point.
  rewrite isolated_interior_set0 set0U.
  rewrite -subset0.
  move=> /= x []/= .
  rewrite inE; move/[dup] => limAx /limit_pointP[a_ [aA anx cvgax]].
  move=> [V].
  rewrite nbhsE/= => -[U [oU Ux] UV VAx].
  have {V UV VAx}UAx : U `&` limit_point (interior A) = [set x].
    rewrite eqEsubset; split.
      rewrite -VAx.
      exact: setSI.
    by rewrite sub1set inE; split.
  pose I_ := open_disjoint_itv oU.
  have := Ux.
  rewrite (open_disjoint_itv_bigcup oU) => -[n _ Inx].
  have In0 : I_ n !=set0 by exists x.
(*  have := nonempty_open_interval_not_subset1 In0 (@open_disjoint_itv_open _ _ oU n) (@open_disjoint_itv_is_interval _ _ oU n).
  move/existsNP => [x0 /existsNP[x1] /not_implyP[Inx0] /not_implyP[Inx1]].
  move/eqP.
  rewrite eq_le.
  move/nandP.
  rewrite -2!ltNge => -[x10|x01].*)
Abort.


End interior_lemmas.

Section continuous_interval.
Context {R : realType}.
Variables (D : set R) (f : R -> R).
Hypothesis cf : {within D, continuous f}.

Lemma is_interval_image_cc a b : `[a, b] `<=` D ->
  is_interval (f @` `[a, b]).
Proof.
have [ab abD|ba _] := leP a b; last first.
  rewrite set_itv_ge// ?bnd_simp -?ltNge// image_set0.
  exact/connected_intervalP/connected0.
move=> _ _/= -[x0 x0ab <-] [x1 x1ab <-] z /andP[fx0z zfx1].
have [x01|x10] := leP x0 x1.
  have [x [xx01 fxz]] : exists2 x : R, x \in `[x0, x1] & f x = z.
    apply: IVT => //.
      apply: continuous_subspaceW cf.
      by apply: subset_trans abD; apply: subset_itv;
        rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
    by rewrite ge_min le_max fx0z/= zfx1 orbT.
  exists x => //.
  by apply: subset_itv xx01; rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
have [x [xx01 fxz]] : exists2 x : R, x \in `[x1, x0] & f x = z.
  apply: IVT => //.
  - exact: ltW.
  - apply: continuous_subspaceW cf.
    by apply: subset_trans abD; apply: subset_itv;
      rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
  by rewrite ge_min le_max fx0z/= zfx1 orbT.
exists x => //.
by apply: subset_itv xx01; rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
Qed.

End continuous_interval.


Section diam.
Context {R : realType}.

Definition diam (A : set R) :=
  if A == set0 then 0%:E else
  ereal_sup ([set `|a.1 - a.2|%:E | a in setX A A]).

Lemma diam0 : diam set0 = 0%:E.
Proof.
by rewrite /diam eqxx.
Qed.

Lemma diam_ge0 (A : set R) : (0 <= diam A)%E.
Proof.
rewrite /diam; case: ifPn => //.
move/set0P => [x Ax].
apply: le_ereal_sup_tmp.
by exists 0 => //; exists (x, x) => /=; rewrite ?subrr ?normr0//.
Qed.

Lemma diamS (A B : set R) : A `<=` B -> (diam A <= diam B)%E.
Proof.
move=> AB.
rewrite {1}/diam; case : ifPn => [_|].
  exact: diam_ge0.
move/set0P => [a Aa].
rewrite /diam; case: ifPn => [|_].
  move/eqP => B0.
  have := AB a Aa.
  by rewrite B0.
apply: ereal_sup_le => r/= [[x y] [/= Ax Ay] <-].
exists (x, y) => //=.
by split; apply: AB.
Qed.

Lemma diam_Rhull (A : set R) : diam [set` Rhull A] = diam A.
Proof.
Admitted.

Lemma diam_closure (A : set R) : diam (closure A) = diam A.
Proof.
have [->|A0] := eqVneq A set0.
  by rewrite closure0.
rewrite -diam_Rhull -(diam_Rhull A).
Admitted.

Lemma diam_itv (x y: R) (b0 b1 : bool) :
  diam [set` (Interval (BSide b0 x) (BSide b1 y))] = `|x - y|%:E.
Proof.
Admitted.

Definition diam_max (s : seq (set R)) := \big[maxe/-oo%E]_(A <- s) (diam A).

Lemma diam_max_ge0 (s : seq (set R)) : s != [::] -> (0 <= diam_max s)%E .
Proof.
case: s => // s0 s1 _.
rewrite /diam_max.
apply: (bigmax_sup_seq _ s0) => //.
  exact: mem_head.
exact: diam_ge0.
Qed.

Lemma diam_max_seq1 (s0 : set R) : diam_max [:: s0] = diam s0.
Proof.
by rewrite /diam_max big_seq1.
Qed.

Lemma diam_max_cons (s0 : set R) (s : seq (set R)) :
  (diam s0 <= diam_max (s0 :: s))%E .
Proof.
apply: (bigmax_sup_seq _ s0) => //.
exact: mem_head.
Qed.

(* unnecessary? *)
Lemma diam_defaultE (s : seq (set R)) :
  s != [::] ->
diam_max s = \big[maxe/0%E]_(A <- s) (diam A).
Proof.
elim: s => // s0 s1 ih _.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: le_bigmax_seq2 => /=.
    by exists s0; rewrite ?mem_head ?leNye.
  move=> i.
  rewrite in_cons => /predU1P[->|is1].
    by exists s0 => //; rewrite mem_head.
  exists i => //.
  by rewrite in_cons is1 orbT.
rewrite big_seq_cond.
apply: bigmax_le.
  exact: diam_max_ge0.
move=> /= A; rewrite andbT in_cons => /predU1P[->|s1A].
  exact: diam_max_cons.
rewrite /diam_max.
rewrite big_cons le_max; apply/orP; right.
have : s1 != [::].
  by apply/negP; move/eqP=> s10; rewrite s10 in s1A.
move/ih; rewrite /diam_max => ->.
exact: le_bigmax_seq.
Qed.

Lemma diam_max0 : diam_max [::] = -oo%E.
Proof.
by rewrite /diam_max big_nil.
Qed.

Lemma diam_maxS (s t : seq (set R)) :
 (forall A, A \in s -> exists2 B, B \in t & A `<=` B) ->
  (diam_max s <= diam_max t)%E.
Proof.
elim: s => //[_|/= s0 s1 ih h].
  by rewrite /diam_max big_nil leNye.
rewrite /diam_max.
rewrite big_cons.
rewrite ge_max; apply/andP; split.
  have [t0 t0t st0] := h s0 (mem_head _ _).
  apply: (@le_trans _ _ (diam t0)).
    exact: diamS.
  exact: le_bigmax_seq.
rewrite big_seq_cond.
apply: bigmax_le.
  exact: leNye.
move=> X.
rewrite andbT => s1X.
have := h X.
rewrite in_cons s1X orbT; move/(_ isT).
move=> [Y s1Y XY].
apply: (@le_trans _ _ (diam Y)).
  exact: diamS.
exact: le_bigmax_seq.
Qed.

End diam.

Module lemma6_direct_new.
Section lemma6_direct.
Context {R : realType}.
Local Notation mu := (@completed_lebesgue_measure R).

Variables a b : R.
Hypothesis ab : a < b.
Variable f : R -> R.
Hypotheses (cf : {within `[a, b], continuous f})
           (bvf : bounded_variation a b f)
           (lusinf : lusinN `[a, b] f).
Definition H := fun x => fine (total_variation a ^~ f x).

(* "Clearly, H is increasing and continuous. " *)
Let ndH := nondecreasing_total_variation bvf.
Let cH : {within `[a, b], continuous H}.
Proof. exact: total_variation_continuous. Qed.

(* https://math.stackexchange.com/questions/1925764/limit-point-of-the-set-of-limit-points-is-in-the-set-of-limit-points *)
Lemma limit_point_redundant (Z : set R) L :
  L = limit_point Z -> limit_point L `<=` L.
(* there is another proof using the fact that limit_point is closed *)
Proof.
move=> LE.
move=> /= p limlimZp.
rewrite LE.
apply/limit_point_open => U pU.
simpl in *.
have [y yp ULy] : exists2 y, y != p & (U `&` L) y.
  have [y [yp Ly Uy]] := limlimZp _ (open_nbhs_nbhs pU).
  by exists y => //.
have [V yV Vp] : exists2 V, nbhs y V & ~ V p.
  have : hausdorff_space R by [].
  rewrite ball_hausdorff => /(_ _ _ yp) -[[r1 r2]/=] => /eqP yr1pr2.
  exists (ball y r1%:num).
    exact: nbhsx_ballx.
  move=> yr1p.
  move: yr1pr2.
  rewrite -subset0.
  move/(_ p).
  by apply; split => //.
have UVy : (U `&` V) y.
  split.
    by case: ULy.
  by apply: nbhs_singleton.
have [z UVZz] : exists z, ((U `&` V) `&` Z) z.
  have : L y by case: ULy.
  rewrite LE.
  rewrite /limit_point/=.
  have : nbhs y (U `&` V).
    apply: filterI => //.
    apply: open_nbhs_nbhs.
    split => //.
      by case: pU.
    by case: UVy.
  move=> /[swap] /[apply] -[z [zy Zz UVz]].
  by exists z; split => //.
have zp : z != p.
  have zV : V z by case: UVZz => -[].
  by apply/eqP => ?; subst z.
exists z; split => //.
by case: UVZz.
by case: UVZz => -[].
Qed.

Definition contiguous_intervals12 (A : set R) :
  nat -> (R * R) :=
  fun n => (contiguous_intervals1 A n, contiguous_intervals2 A n).

Lemma contiguous_intervals_Rhull (A : set R) (cA : closed A) :
  \bigcup_k contiguous_intervals A k `|` A = [set` Rhull A].
Proof.
rewrite -bigcup_contiguous_intervals//.
by rewrite /cplt_hull setDKU//; exact: sub_Rhull.
Qed.

Lemma contiguous_intervals2_notin (Z : set R) : has_ubound Z -> forall j,
  ((contiguous_intervals2 Z j))
    \notin `]contiguous_intervals1 Z j, contiguous_intervals2 Z j[.
Proof.
move=> ubZ j.
rewrite in_itv/=.
by rewrite ltxx andbF.
Qed.

Lemma contiguous_intervals1_notin (Z : set R) : has_lbound Z -> forall j,
  ((contiguous_intervals1 Z j))
    \notin `]contiguous_intervals1 Z j, contiguous_intervals2 Z j[.
Proof.
move=> lbZ j.
rewrite in_itv/=.
by rewrite ltxx/=.
Qed.

Lemma set1_not_open (x : R) : ~ open [set x].
Proof. by rewrite openE/= interior_set1 => /(_ x); exact. Qed.

Lemma is_subset1_set1 (A : set R) :
  A !=set0 -> is_subset1 A -> exists x, A = [set x].
Proof.
move=> [x Ax] A1; exists x; apply/seteqP; split => [|y ->//].
by move=> y Ay; exact: A1.
Qed.

Lemma contiguous_intervals2_notin' (Z : set R) j l : compact Z ->
  contiguous_intervals Z j !=set0 ->
  j != l ->
  ((contiguous_intervals2 Z j))
    \notin `]contiguous_intervals1 Z l, contiguous_intervals2 Z l[.
Proof.
move=> /[dup] cZ; rewrite Rcompact_boundE/= => -[closeZ uZ lZ] Zj0 j_neq_l.
rewrite in_itv/=.
rewrite negb_and -[X in _ || X]leNgt -implybE; apply/implyP.
rewrite fine_contiguous_intervals2// fine_contiguous_intervals1// => lj.
rewrite !fine_contiguous_intervals2//.
rewrite leNgt; apply/negP => jl.
have H : contiguous_intervals Z j `&` contiguous_intervals Z l = set0.
  have /trivIsetP := @disjoint_contiguous_intervals _ Z.
  exact.
move: (H).
apply/eqP/set0P.
have ? : inf (contiguous_intervals Z j) < sup (contiguous_intervals Z j).
  apply: has_bound_not_subset1_inf_sup.
  exact: has_lbound_contiguous_intervals.
  exact: has_ubound_contiguous_intervals.
  move/is_subset1_set1 => /(_ Zj0)[x Zj1].
  have := @open_contiguous_intervals _ Z j.
  by rewrite Zj1; exact: set1_not_open.
have H1 : inf (contiguous_intervals Z j) < inf (contiguous_intervals Z l).
  rewrite ltNge; apply/negP => lj'.
  move: H.
  apply/eqP/set0P.
  pose m := (inf (contiguous_intervals Z j) + sup (contiguous_intervals Z j)) / 2.
  exists m; split.
    rewrite contiguous_ooitv//= in_itv/=.
    rewrite fine_contiguous_intervals1//.
    rewrite fine_contiguous_intervals2//.
    by rewrite !midf_lt//=.
  rewrite contiguous_ooitv//= in_itv/=.
  rewrite fine_contiguous_intervals1//.
  rewrite fine_contiguous_intervals2//.
  apply/andP; split.
    rewrite /m.
    by rewrite (le_lt_trans lj')// midf_lt.
  rewrite (le_lt_trans _ jl)// midf_le//.
  exact/ltW.
pose m : R := (inf (contiguous_intervals Z l) + sup (contiguous_intervals Z j)) / 2.
exists m; split.
  rewrite contiguous_ooitv//= in_itv/=.
  rewrite fine_contiguous_intervals1//.
  rewrite fine_contiguous_intervals2//.
  rewrite !midf_lt// andbT.
  rewrite /m.
  rewrite (lt_le_trans H1)//.
  by rewrite midf_le// ltW.
rewrite contiguous_ooitv//= in_itv/=.
rewrite fine_contiguous_intervals1//.
rewrite  fine_contiguous_intervals2//.
rewrite !midf_lt//=.
rewrite (le_lt_trans _ jl)// midf_le//.
exact: ltW.
Qed.

Lemma contiguous_intervals1_notin' (Z : set R) j l : compact Z ->
  contiguous_intervals Z j !=set0 ->
  j != l ->
  ((contiguous_intervals1 Z j))
    \notin `]contiguous_intervals1 Z l, contiguous_intervals2 Z l[.
Proof.
move=> /[dup] cZ; rewrite Rcompact_boundE/= => -[closeZ uZ lZ] Zj0 j_neq_l.
rewrite in_itv//=.
rewrite negb_and -[X in _ || X]leNgt -implybE; apply/implyP.
rewrite fine_contiguous_intervals1// fine_contiguous_intervals1// => lj.
rewrite leNgt; apply/negP => jl.
have H : contiguous_intervals Z j `&` contiguous_intervals Z l = set0.
  have /trivIsetP := @disjoint_contiguous_intervals _ Z.
  exact.
move: (H).
apply/eqP/set0P.
have ? : inf (contiguous_intervals Z j) < sup (contiguous_intervals Z j).
  apply: has_bound_not_subset1_inf_sup.
  exact: has_lbound_contiguous_intervals.
  exact: has_ubound_contiguous_intervals.
  move/is_subset1_set1 => /(_ Zj0)[x Zj1].
  have := @open_contiguous_intervals _ Z j.
  by rewrite Zj1; exact: set1_not_open.
have H1 : sup (contiguous_intervals Z l) < sup (contiguous_intervals Z j).
  rewrite ltNge; apply/negP => lj'.
  move: H.
  apply/eqP/set0P.
  pose m := (inf (contiguous_intervals Z j) + sup (contiguous_intervals Z j)) / 2.
  exists m; split.
    rewrite contiguous_ooitv//= in_itv/=.
    rewrite fine_contiguous_intervals1//.
    rewrite fine_contiguous_intervals2//.
    by rewrite !midf_lt//=.
  rewrite contiguous_ooitv//= in_itv/=.
  rewrite fine_contiguous_intervals1//.
  rewrite fine_contiguous_intervals2//.
  apply/andP; split.
    rewrite /m.
    rewrite (lt_le_trans lj)// midf_le//.
    exact/ltW.
  rewrite /m.
  by rewrite (lt_le_trans _ lj')// midf_lt//.
pose m : R := (inf (contiguous_intervals Z j) + sup (contiguous_intervals Z l)) / 2.
exists m; split.
  rewrite contiguous_ooitv//= in_itv/=.
  rewrite fine_contiguous_intervals1//.
  rewrite fine_contiguous_intervals2//.
  rewrite !midf_lt//=.
  rewrite /m.
  rewrite (le_lt_trans _ H1)//.
  by rewrite midf_le// ltW.
rewrite contiguous_ooitv//= in_itv/=.
rewrite fine_contiguous_intervals1//.
rewrite fine_contiguous_intervals2//.
rewrite !midf_lt//= andbT.
rewrite /m.
rewrite (lt_le_trans lj)// midf_le//.
exact: ltW.
Qed.

Lemma closureN (A : set R) r : closure (-%R @` A) (- r) <-> closure A r.
Proof.
split.
- rewrite /closure/= => rA B rB.
  have /rA : nbhs (- r) (-%R @` B) by rewrite nbhsNimage/=; exists B.
  move=> [_/= [[xA Ax <-]]] [y By /eqP]; rewrite eqr_opp => /eqP ?; subst y.
  by exists xA.
- rewrite /closure/= => rA B rB.
  have /rA : nbhs r (-%R @` B).
    by move: rB; rewrite nbhsNimage/= => -[C rC <-]; rewrite setNK.
  move=> [x [Ax/= [y By]]] ?; subst x.
  exists y; split => //=.
  by exists (- y) => //; rewrite opprK.
Qed.

(* TODO: PR *)
Lemma closure_inf (A : set R) : A !=set0 -> has_lbound A -> closure A (inf A).
Proof.
move=> /nonemptyN A0 /has_lb_ubN lbndA.
have /closureN := closure_sup A0 lbndA.
by rewrite -/(inf A) setNK.
Qed.

Lemma compact_Rhull (Z : set R) : compact Z -> Z !=set0 -> Rhull Z = `[inf Z, sup Z].
Proof.
rewrite Rcompact_boundE/= => -[closedZ ubndZ lbndZ] Z0.
rewrite /Rhull !(introT (@asboolP _) _)//.
- rewrite {1}((closure_id _).1 closedZ).
  exact: closure_sup.
- rewrite {1}((closure_id _).1 closedZ).
  by apply: closure_inf.
Qed.

Lemma mem_contiguous_intervals2 (Z : set R) j :
  compact Z ->
  Z !=set0 ->
  contiguous_intervals Z j !=set0 ->
  Z ((contiguous_intervals2 Z j)).
Proof.
move=> cZ Z0 Zj0.
move: (cZ); rewrite Rcompact_boundE/= => -[closedZ ubndZ lbndZ].
have cpltZE := bigcup_contiguous_intervals closedZ.
have H1 : (cplt_hull Z) =
    \bigcup_k `]contiguous_intervals1 Z k, contiguous_intervals2 Z k[%classic.
  rewrite [in LHS]cpltZE; apply: eq_bigcup => // i _.
  by rewrite contiguous_ooitv.
have : (~` (cplt_hull Z)) (sup (contiguous_intervals Z j)).
  move=> H2.
  have : ((cplt_hull Z)) (sup (contiguous_intervals Z j)).
    by [].
  rewrite H1 => -[l _].
  apply/negP.
  rewrite -fine_contiguous_intervals2//.
  have [->{l}|ij] := eqVneq l j.
    exact: contiguous_intervals2_notin.
  apply: contiguous_intervals2_notin' => //.
  by rewrite eq_sym.
rewrite fine_contiguous_intervals2//.
rewrite /cplt_hull setCD => -[/=|//].
have : sup (contiguous_intervals Z j) \in [set` Rhull Z].
  have H3 : (closure (contiguous_intervals Z j)) (sup (contiguous_intervals Z j)).
    apply: closure_sup => //.
    exact: has_ubound_contiguous_intervals.
  have H4 : closure (contiguous_intervals Z j) `<=` [set` Rhull Z].
    rewrite [X in _ `<=` X](closure_id _).1//; last first.
      rewrite compact_Rhull//.
      exact: itv_closed_ends_closed.
    apply: (@subset_trans _ (closure (cplt_hull Z))).
      rewrite cpltZE.
      apply: closureS.
      by apply: bigcup_sup.
    apply: closureS.
    by apply: cplt_hull_subset_Rhull.
  have := H4 _ H3.
  by rewrite /= inE.
by rewrite inE  =>  ->.
Qed.

Lemma mem_contiguous_intervals1 (Z : set R) j :
  compact Z ->
  Z !=set0 ->
  contiguous_intervals Z j !=set0 ->
  Z ((contiguous_intervals1 Z j)).
Proof.
move=> cZ Z0 Zj0.
move: (cZ); rewrite Rcompact_boundE/= => -[closedZ ubndZ lbndZ].
have cpltZE := bigcup_contiguous_intervals closedZ.
have H1 : (cplt_hull Z) =
    \bigcup_k `]contiguous_intervals1 Z k, contiguous_intervals2 Z k[%classic.
  rewrite [in LHS]cpltZE; apply: eq_bigcup => // i _.
  by rewrite contiguous_ooitv.
have : (~` (cplt_hull Z)) (inf (contiguous_intervals Z j)).
  move=> H2.
  have : ((cplt_hull Z)) (inf (contiguous_intervals Z j)).
    by [].
  rewrite H1 => -[l _].
  apply/negP.
  rewrite -fine_contiguous_intervals1//.
  have [->{l}|ij] := eqVneq l j.
    exact: contiguous_intervals1_notin.
  apply: contiguous_intervals1_notin' => //.
  by rewrite eq_sym.
rewrite fine_contiguous_intervals1//.
rewrite /cplt_hull setCD => -[/=|//].
have : inf (contiguous_intervals Z j) \in [set` Rhull Z].
  have H3 : (closure (contiguous_intervals Z j)) (inf (contiguous_intervals Z j)).
    apply: closure_inf => //.
    exact: has_lbound_contiguous_intervals.
  have H4 : closure (contiguous_intervals Z j) `<=` [set` Rhull Z].
    rewrite [X in _ `<=` X](closure_id _).1//; last first.
      rewrite compact_Rhull//.
      exact: itv_closed_ends_closed.
    apply: (@subset_trans _ (closure (cplt_hull Z))).
      rewrite cpltZE.
      apply: closureS.
      by apply: bigcup_sup.
    apply: closureS.
    by apply: cplt_hull_subset_Rhull.
  have := H4 _ H3.
  by rewrite /= inE.
by rewrite inE  =>  ->.
Qed.

Definition contiguous_intervals_support (U : set R) : set nat :=
  [set i | contiguous_intervals U i !=set0].

Lemma bigcup_contiguous_intervals_support (P : set R) :
  \bigcup_k contiguous_intervals P k =
  \bigcup_(k in contiguous_intervals_support P) contiguous_intervals P k.
Proof.
rewrite [RHS]bigcup_mkcond.
apply: eq_bigcupr => i _.
case: ifPn => //.
rewrite notin_setE /contiguous_intervals_support/=.
by move/set0P/negP/negPn/eqP.
Qed.

Lemma lebesgue_measure_gt0 (P : set R) :
  compact P -> is_interval P -> P !=set0 -> ~ is_subset1 P ->
  (0 < lebesgue_measure P)%E.
Proof.
rewrite Rcompact_boundE => /= -[closedP ubndP lbndP].
move/is_intervalP => PE P0 P1.
rewrite PE compact_Rhull//; last by rewrite Rcompact_boundE.
rewrite lebesgue_measure_itv/= lte_fin -EFinD.
rewrite has_bound_not_subset1_inf_sup//.
by rewrite lte_fin subr_gt0 has_bound_not_subset1_inf_sup.
Qed.

Lemma is_subset1_isolated (r : R) : isolated [set r] = [set r].
Proof.
apply/seteqP; split; first exact: isolatedS.
move=> _/= ->; split => /=.
  by rewrite inE.
exists (ball r 1) => //.
  exact: nbhsx_ballx.
rewrite setIidr// => _ ->.
exact: ballxx.
Qed.

Lemma perfect_set1 (r : R) : ~ perfect_set [set r].
Proof.
move/perfectP => -[_].
rewrite is_subset1_isolated.
move=> /eqP; apply/negP/set0P.
by exists r.
Qed.

Lemma snd_map (l : seq (R * R)) i : (i < size l)%N ->
  (l`_i).2 = (map snd l)`_i.
Proof. by move=> ?; rewrite (nth_map 0). Qed.

Lemma fst_map (l : seq (R * R)) i : (i < size l)%N ->
  (l`_i).1 = (map fst l)`_i.
Proof. by move=> ?; rewrite (nth_map 0). Qed.

Lemma nth_set (P : set R) (l : seq R) i : (i < size l)%N ->
  [set` l] `<=` P -> P (nth 0 l i).
Proof.
move=> li lA.
by have /lA := mem_nth 0 li.
Qed.

Lemma sort_sorted_fst (p : seq (R * R)) :
  let le1 := (fun x y : R * R => x.1 <= y.1) in
  sorted le1 p -> sorted <=%R [seq i.1 | i <- p].
Proof.
elim: p => // h t ih le1 /= le1ht.
move/path_sorted : (le1ht) => /ih {}ih.
rewrite path_sortedE; last exact: le_trans.
rewrite ih andbT.
apply/allP => x /mapP[/= i it ->].
rewrite path_sortedE in le1ht; last first.
  move=> u v w; rewrite /lt1 => vu uw.
  exact: (le_trans vu).
by move/andP : le1ht => [/allP] => /(_ _ it).
Qed.

Lemma sort_sorted_fst_iota (p : seq (R * R)) n :
  let le1 := (fun x y : R * R => x.1 <= y.1) in
  sorted le1 p ->
  size p = n ->
  sorted <=%R [seq (p`_i).1 | i <- iota 0 n].
Proof.
move=> le1 le1p pn.
rewrite (map_comp fst).
apply: sort_sorted_fst.
rewrite -/lt1 -pn.
by rewrite map_nth_iota ?subn0// drop0 take_size.
Qed.

Lemma contiguous_intervals_sort' (P : set R) i j :
  has_lbound P -> has_ubound P ->
  contiguous_intervals P j !=set0 ->
  contiguous_intervals1 P i <= contiguous_intervals1 P j ->
  contiguous_intervals2 P i <= contiguous_intervals2 P j.
Proof.
move=> lbP ubP Pj0 infsupi.
have ? : has_lbound (contiguous_intervals P i).
  exact: has_lbound_contiguous_intervals.
have ? : has_ubound (contiguous_intervals P i).
  exact: has_ubound_contiguous_intervals.
have ? : has_lbound (contiguous_intervals P j).
  exact: has_lbound_contiguous_intervals.
have ? : has_ubound (contiguous_intervals P j).
  exact: has_ubound_contiguous_intervals.
have H1 : (contiguous_intervals1 P i) <= (contiguous_intervals2 P i).
  by rewrite has_bound_inf_sup.
have H2 : (contiguous_intervals1 P j) <= (contiguous_intervals2 P j).
  by rewrite has_bound_inf_sup.
have [->//|ij] := eqVneq i j.
move: H2; rewrite le_eqVlt => /predU1P[H2|H2].
  move: Pj0.
  by rewrite contiguous_ooitv// H2 set_itv_ge ?bnd_simp// => -[].
rewrite leNgt; apply/negP => abs.
have /trivIsetP/(_ i j Logic.I Logic.I ij) := @disjoint_contiguous_intervals _ P.
pose x := ((contiguous_intervals1 P j + contiguous_intervals2 P j))/2.
rewrite -subset0.
move=> /(_ x)[].
split.
  rewrite contiguous_ooitv//= in_itv/= /x.
  apply/andP; split.
    rewrite (le_lt_trans infsupi)//.
    by rewrite midf_lt//.
  rewrite (le_lt_trans _ abs)//.
  by rewrite midf_le// ltW.
rewrite contiguous_ooitv//= in_itv/= /x.
apply/andP; split.
  by rewrite midf_lt//.
by rewrite midf_lt.
Qed.

Lemma contiguous_intervals_sort (P : set R) p :
  has_lbound P -> has_ubound P ->
  contiguous_intervals_support P = [set` p] ->
  sorted <=%R [seq contiguous_intervals1 P j | j <- p] ->
  sorted <=%R [seq contiguous_intervals2 P j | j <- p].
Proof.
case: p => // h t lbP ubP Pp sorted1.
apply/(sortedP 0) => i.
rewrite size_map [in X in X -> _]/= ltnS => ti.
rewrite (nth_map 0)//; last by rewrite /= ltnW.
rewrite (nth_map 0)//.
apply: contiguous_intervals_sort' => //.
  move/seteqP : Pp => [_] => /(_ (t`_i)).
  rewrite /contiguous_intervals_support/=.
  apply.
  rewrite inE; apply/orP; right.
  apply/(nthP 0).
  by exists i.
move/(sortedP 0) : sorted1 => /(_ i).
rewrite size_map [in X in (X -> _) -> _]/= ltnS => /(_ ti).
rewrite (nth_map 0)//.
  by rewrite (nth_map 0)//.
by rewrite /= ltnS ltnW.
Qed.

Lemma setD_bigcup_itvoo (c d : R) (a_ b_ : R^nat) n :
  (forall i, (i < n.+1)%N -> a_ i \in `[c, d]) ->
  (forall i, (i < n.+1)%N -> b_ i \in `[c, d]) ->
  sorted <=%R [seq a_ i | i <- iota 0 n.+1] ->
  sorted <=%R [seq b_ i | i <- iota 0 n.+1] ->
  (forall i, (i < n)%N -> b_ i <= a_ i.+1) ->
  `[c, d] `\` \big[setU/set0]_(i < n.+1) `]a_ i, b_ i[%classic =
  `[c, a_ 0]  `|`
  \big[setU/set0]_(i < n) `[b_ i, a_ i.+1]%classic `|`
  `[b_ n, d].
Proof.
elim: n c d a_ b_ => [c d a_ b_ acd bcd sorteda sortedb blea|].
  rewrite big_ord0 setU0 big_ord_recl/= big_ord0 setU0.
  rewrite setDE setCitv/= setIUr; congr setU.
  - rewrite -itv_setI/=.
    rewrite /Order.meet/=.
    rewrite meet_r ?bnd_simp//.
    by rewrite (itvP (acd 0 _)).
  - rewrite -itv_setI/=.
    rewrite /Order.meet/=.
    rewrite meet_l//.
    rewrite join_r ?bnd_simp//.
    by rewrite (itvP (bcd 0 _)).
move=> n ih c d a_ b_ acd bcd sorteda sortedb blea.
rewrite big_ord_recr/=.
rewrite setDE.
rewrite setCU.
rewrite setIA.
rewrite setIAC.
rewrite (_ : `[c, d] `&` _ = `[c, a_ n.+1] `|` `[b_ n.+1, d]); last first.
  rewrite setCitv//= setIUr.
  rewrite -!itv_setI/=.
  rewrite /Order.meet/=.
  rewrite meet_r ?bnd_simp//; last first.
    by rewrite (itvP (acd _ _)).
  rewrite join_l//.
  rewrite meet_l ?bnd_simp//.
  rewrite join_r// bnd_simp.
  by rewrite (itvP (bcd _ _)).
rewrite setIUl.
rewrite -setDE.
rewrite ih//; last 5 first.
- move=> i ni.
  rewrite in_itv/=.
  rewrite (itvP (acd _ _))/=; last by rewrite (ltn_trans ni).
  have := sorted_leq_nth le_trans lexx 0 sorteda i n.+1.
  rewrite !inE !size_map size_iota.
  move=> /(_ (ltnW ni) ltac:(by []) (ltnW ni)).
  rewrite (nth_map 0) ?size_iota; last exact: ltnW.
  rewrite nth_iota//; last exact: ltnW.
  by rewrite (nth_map 0) ?size_iota// nth_iota//.
- move=> i ni.
  rewrite in_itv/=.
  rewrite (itvP (bcd _ _))/=; last by rewrite ltnS ltnW.
  rewrite (le_trans (blea i _))//.
  have [->//|] := eqVneq i n.
  rewrite eq_le negb_and -!ltNge => /orP[|].
    rewrite ltEnat/= => ltni.
    have := leq_trans ni ltni.
    by rewrite ltnn.
  rewrite ltEnat/= => ltni.
  have := sorted_leq_nth le_trans lexx 0 sorteda i.+1 n.+1.
  rewrite !inE !size_map size_iota.
  move=> /(_ (ltnSE ni) ltac:(by []) ni).
  rewrite (nth_map 0) ?size_iota; last exact: ltnW.
  rewrite nth_iota//.
  by rewrite (nth_map 0) ?size_iota// nth_iota//.
- apply: subseq_sorted sorteda.
    exact: le_trans.
  apply: map_subseq.
  rewrite -(addn1 n.+1).
  rewrite iotaD.
  exact: prefix_subseq.
- apply: subseq_sorted sortedb.
    exact: le_trans.
  apply: map_subseq.
  rewrite -(addn1 n.+1).
  rewrite iotaD.
  exact: prefix_subseq.
- move=> k kn.
  apply: blea.
  by rewrite ltnS ltnW.
rewrite [in RHS]big_ord_recr/=.
rewrite -!setUA.
congr setU.
congr setU.
congr setU.
rewrite setIidl//.
apply: subsetCr.
rewrite -[X in X `<=` _](bigcup_mkord _ (fun i => `]a_ i, b_ i[%classic)).
move=> r [i ni/= rab].
rewrite in_itv/=.
apply/negP; rewrite negb_and; apply/orP; left.
rewrite -ltNge.
rewrite (@lt_le_trans _ _ (b_ i))//.
  by rewrite (itvP rab).
have := sorted_leq_nth le_trans lexx 0 sortedb i n.+1.
rewrite !inE !size_map size_iota.
move=> /(_ (ltnW ni) ltac:(by []) (ltnW ni)).
rewrite !(nth_map 0) ?size_iota//; last exact: ltnW.
by rewrite !nth_iota//; last exact: ltnW.
Qed.

Lemma finite_seqP_new {T : eqType} A :
   finite_set A <-> exists2 s : seq T, uniq s & A = [set` s].
Proof.
elim/eqPchoice: T => T in A *; rewrite finite_fsetP.
split=> [[X ->]|[s us ->]]; first by exists X.
by exists [fset x | x in s]%fset; apply/seteqP; split=> x /=; rewrite inE.
Qed.

Lemma contiguous_infinite (P : set R) :
  P `<=` `[a, b] ->
  compact P ->
  P !=set0 ->
  lebesgue_measure P = 0 ->
  perfect_set P ->
  infinite_set (contiguous_intervals_support P).
Proof.
move=> Pab compactP P0 muP perfectP.
have closedP : closed P by case: perfectP.
pose U := cplt_hull P.
have openU : open U by apply: closed_open_cplt_hull.
have UE := open_disjoint_itv_bigcup openU.
move=> /finite_seqP_new[/= p up Pp].
have [p0|p0] := eqVneq p [::].
  have : contiguous_intervals_support P = set0.
    by rewrite Pp p0 -subset0 => x/=; rewrite inE.
  have := bigcup_contiguous_intervals closedP.
  rewrite -/U bigcup_contiguous_intervals_support.
  rewrite Pp p0 bigcup0// setD_eq0 => {}Pp _.
  have {}Pp : P = [set` Rhull P] by apply/seteqP; split => //; exact: sub_Rhull.
  move/is_intervalP : Pp => itv_P.
  have : ~ is_subset1 P.
    move/is_subset1_set1 => /(_ P0)[r Pr].
    move: perfectP.
    rewrite Pr.
    exact: perfect_set1.
  move/lebesgue_measure_gt0 => /(_ compactP itv_P P0).
  by rewrite muP ltxx.
have := bigcup_contiguous_intervals_fine compactP.
rewrite -/U => {}UE.
have {}UE : U = \big[setU/set0]_(k <- p)
    `](contiguous_intervals1 P k), (contiguous_intervals2 P k)[%classic.
  rewrite -bigcup_seq bigcup_mkcond UE; apply: eq_bigcupr => i _.
  case: ifPn => //.
  rewrite -Pp notin_setE.
  rewrite /contiguous_intervals_support/= => /nonemptyPn.
  rewrite /contiguous_intervals1 /contiguous_intervals2/= => ->/=.
  by rewrite inf0 sup0 set_itv_ge// bnd_simp ltxx.
pose unsorted_bnds := [seq ((contiguous_intervals1 P i),
                            (contiguous_intervals2 P i)) | i <- p].
pose le1 := fun x y : R * R => x.1 <= y.1.
have total_le1 : total le1.
  move=> [x1 x2] [y1 y2].
  by rewrite /le1/= le_total.
pose sorted_bnds := sort le1 unsorted_bnds.
have [h hsorted_bnds] := perm_iota_sort le1 0 unsorted_bnds.
rewrite -/sorted_bnds; move=> /= sorted_bndsE.
have {}UE : U = \big[setU/set0]_(k < size p)
    `](nth 0 sorted_bnds k).1, (nth 0 sorted_bnds k).2[%classic.
  rewrite UE.
  have pE : p = map (fun i => nth 0 p i) (iota 0 (size p)).
    by rewrite map_nth_iota ?subn0// drop0 take_size.
  rewrite [in LHS](perm_big [seq p`_i | i <- h])//=; last first.
    rewrite {1}pE.
    apply: perm_map.
    by rewrite perm_sym (perm_trans hsorted_bnds)// size_map.
  rewrite big_map.
  apply/esym.
  rewrite -(big_mkord xpredT (fun k => `](sorted_bnds`_k).1, (sorted_bnds`_k).2[%classic)).
  rewrite (_ : size p = size sorted_bnds); last first.
    by rewrite pE size_map size_iota size_sort size_map.
  rewrite -(@big_nth _ set0 setU _ 0 sorted_bnds xpredT (fun i => `]i.1, i.2[%classic)).
  rewrite sorted_bndsE big_map//.
  rewrite big_seq [in RHS]big_seq; apply: eq_bigr => /= i ih.
  have ip : (i < size p)%N.
    have := perm_mem hsorted_bnds => /(_ i).
    by rewrite ih mem_iota leq0n add0n/= size_map => <-.
  by rewrite (nth_map 0).
pose n := size p.
have PU : P = [set` Rhull P] `\` U.
  by rewrite /U /cplt_hull setDD setIidr//; exact: sub_Rhull.
have L3 : forall i, (i < (size p).-1)%N ->
  exists2 j, (j < size p)%N & unsorted_bnds`_j = sorted_bnds`_i.
  move=> i0 i0p.
  have K1 : sorted_bnds`_i0 \in unsorted_bnds.
    (* TODO: too long! *)
    rewrite sorted_bndsE.
    rewrite (nth_map 0); last first.
      by rewrite (perm_size hsorted_bnds) size_iota size_map (leq_trans i0p)// leq_pred.
    apply/(nthP 0).
    exists (h`_i0) => //.
    have : h`_i0 \in h.
      apply/(nthP 0); exists i0 => //.
      by rewrite (perm_size hsorted_bnds) size_iota size_map (leq_trans i0p)// leq_pred.
    by rewrite (perm_mem hsorted_bnds) mem_iota leq0n add0n/=.
  move: K1 => /(nthP 0)[j]; rewrite size_map => Hj HjE.
  by exists j.
have L4 : forall i, (i < (size p).-1)%N ->
  exists2 j, (j < size p)%N & unsorted_bnds`_j = sorted_bnds`_i.+1.
  move=> i0 i0p.
  have K2 : sorted_bnds`_i0.+1 \in unsorted_bnds.
    rewrite sorted_bndsE.
    rewrite (nth_map 0); last first.
      rewrite (perm_size hsorted_bnds) size_iota size_map.
      by rewrite -(@prednK (size p))// lt0n size_eq0.
    apply/(nthP 0); exists (h`_i0.+1) => //.
    rewrite size_map.
    have : h`_i0.+1 \in h.
      apply/(nthP 0); exists i0.+1 => //.
      rewrite (perm_size hsorted_bnds) size_iota size_map.
      by rewrite -(@prednK (size p))// lt0n size_eq0.
    rewrite (perm_mem hsorted_bnds) mem_iota leq0n add0n/=.
    by rewrite size_map.
  move: K2 => /(nthP 0)[k]; rewrite size_map => Hk HkE.
  by exists k.
have L5 : forall i, (i < size p)%N ->
    exists2 j, (j \in p)%N &
      (sorted_bnds`_i) = (contiguous_intervals1 P j, contiguous_intervals2 P j).
    move=> i pi.
    have hih : nth 0 h i \in h.
      apply/(nthP 0); exists i => //.
      by rewrite (perm_size hsorted_bnds) size_iota size_map.
    exists (nth 0 p (nth 0 h i)) => //.
      apply/(nthP 0).
      exists (h`_i) => //.
      move: hih.
      by rewrite (perm_mem hsorted_bnds) mem_iota add0n leq0n/= size_map.
    rewrite sorted_bndsE (nth_map 0)//; last first.
      by rewrite (perm_size hsorted_bnds)// size_iota size_map.
    rewrite (nth_map 0)//.
    move: hih.
    by rewrite (perm_mem hsorted_bnds) mem_iota add0n leq0n/= size_map.
have {}UE : [set` Rhull P] `\` U = `[inf P, (nth 0 sorted_bnds 0).1]%classic
    `|` (\big[setU/set0]_(k < n.-1)
        `[(nth 0 sorted_bnds k).2, (nth 0 sorted_bnds k.+1).1]%classic)
    `|` `[(nth 0 sorted_bnds n.-1).2, sup P]%classic.
  rewrite [in LHS]UE.
  rewrite -[in LHS](@prednK (size p)); last by rewrite lt0n size_eq0.
  rewrite compact_Rhull//.
  have itv_neq0 x : x \in unsorted_bnds -> `]x.1, x.2[ !=set0.
    rewrite /= => /mapP[/= i ip ->/=].
    have : contiguous_intervals_support P i by rewrite Pp/=.
    rewrite /contiguous_intervals_support/=.
    rewrite -contiguous_ooitv//.
      exact: (subset_has_ubound Pab).
    exact: (subset_has_lbound Pab).
  have sort1 : [seq (sorted_bnds`_i).1 | i <- iota 0 (size p)] =
               sort <=%R [seq contiguous_intervals1 P i | i <- p].
    rewrite (map_comp fst).
    rewrite map_nth_iota; last first.
      by rewrite subn0 size_sort size_map.
    rewrite drop0.
    rewrite (_ : size p = size sorted_bnds)//; last first.
      by rewrite size_sort size_map.
    rewrite take_size.
    rewrite /sorted_bnds.
    rewrite -sort_map.
    congr sort.
    rewrite /unsorted_bnds.
    rewrite -(map_comp fst)/=.
    by apply: eq_map => x/=.
  have H1 : sorted <=%R [seq (sorted_bnds`_i).1 | i <- iota 0 (size p)].
    rewrite sort_sorted_fst_iota//; last by rewrite /sorted_bnds size_sort size_map.
    by apply: sort_sorted; exact: total_le1.
  rewrite (@setD_bigcup_itvoo _ _ (fun k => (sorted_bnds`_k).1)
                              (fun k => (sorted_bnds`_k).2))//; last 4 first.
  - move=> i.
    rewrite prednK; last by rewrite lt0n size_eq0.
    move=> ip.
    have [j [jp ij]] := L5 _ ip.
    rewrite ij -compact_Rhull//.
    apply/sub_Rhull.
    apply: mem_contiguous_intervals2 => //.
    rewrite contiguous_ooitv//; last 2 first.
      exact: (subset_has_ubound Pab).
      exact: (subset_has_lbound Pab).
    have : (contiguous_intervals1 P j, contiguous_intervals2 P j) \in unsorted_bnds.
      rewrite -ij sorted_bndsE (nth_map 0); last first.
        by rewrite (perm_size hsorted_bnds)// size_iota size_map.
      apply/(nthP 0); exists (nth 0 h i) => //.
      rewrite size_map.
      have : nth 0 h i \in h.
        apply/(nthP 0); exists i => //.
        by rewrite (perm_size hsorted_bnds) size_iota size_map.
      by rewrite (perm_mem hsorted_bnds) mem_iota add0n leq0n/= size_map.
    by move/itv_neq0 => /=.
  - by rewrite prednK; last by rewrite lt0n size_eq0.
  - rewrite prednK; last by rewrite lt0n size_eq0.
    pose q := [seq nth 0 p i | i <- h].
    have pq : size q = size p.
      by rewrite /q size_map (perm_size hsorted_bnds) size_iota size_map.
    have [qE1 qE2] :
        [seq (sorted_bnds`_i).1 | i <- iota 0 (size p)] =
        [seq contiguous_intervals1 P i | i <- q] /\
        [seq (sorted_bnds`_i).2 | i <- iota 0 (size p)] =
        [seq contiguous_intervals2 P i | i <- q].
      split.
        rewrite [in LHS]sorted_bndsE.
        rewrite (map_comp fst).
        rewrite map_nth_iota; last first.
          by rewrite size_map subn0 (perm_size hsorted_bnds) size_iota size_map.
        rewrite drop0.
        rewrite (_ : size p = size ([seq unsorted_bnds`_i | i <- h])); last first.
          by rewrite size_map (perm_size hsorted_bnds) size_iota size_map.
        rewrite take_size.
        rewrite -(map_comp fst)/=.
        rewrite -map_comp/=.
        apply/eq_in_map => // x/= zh.
        rewrite /unsorted_bnds/=.
        rewrite (nth_map 0)//=.
        rewrite -pq size_map.
        move: zh.
        rewrite (perm_mem hsorted_bnds) mem_iota leq0n add0n/= size_map.
        by rewrite (perm_size hsorted_bnds) size_iota size_map.
      rewrite [in LHS]sorted_bndsE.
      rewrite (map_comp snd).
      rewrite map_nth_iota; last first.
        by rewrite size_map subn0 (perm_size hsorted_bnds) size_iota size_map.
      rewrite drop0.
      rewrite (_ : size p = size ([seq unsorted_bnds`_i | i <- h])); last first.
        by rewrite size_map (perm_size hsorted_bnds) size_iota size_map.
      rewrite take_size.
      rewrite -(map_comp snd)/=.
      rewrite -map_comp/=.
      apply/eq_in_map => // x/= zh.
      rewrite /unsorted_bnds/=.
      rewrite (nth_map 0)//=.
      rewrite -pq size_map.
      move: zh.
      rewrite (perm_mem hsorted_bnds) mem_iota leq0n add0n/= size_map.
      by rewrite (perm_size hsorted_bnds) size_iota size_map.
    rewrite qE2.
    apply: contiguous_intervals_sort => //.
    by move: compactP; rewrite Rcompact_boundE => -[].
    by move: compactP; rewrite Rcompact_boundE => -[].
    have ->// : [set` q] = [set` p].
    apply/seteqP; split.
      move=> /=r /mapP[/= i].
      rewrite (perm_mem hsorted_bnds) mem_iota leq0n/= add0n.
      rewrite size_map => pi ->.
      by apply/(nthP 0); exists i.
    move=> /= i /(nthP 0)[j jp <-].
    apply/mapP; exists j => //.
    rewrite (perm_mem hsorted_bnds) mem_iota leq0n/= add0n.
    by rewrite size_map.
    by rewrite -qE1.
  - move=> i pi.
    have ? : (i < size p)%N by rewrite (leq_trans pi)// leq_pred.
    have ? : (i.+1 < size p)%N by rewrite -(@prednK (size p)) ?lt0n ?size_eq0.
    have H2 : (sorted_bnds`_i).1 <= (sorted_bnds`_i.+1).1.
      rewrite fst_map; last by rewrite size_sort size_map.
      rewrite fst_map; last by rewrite size_sort size_map.
      apply: sorted_leq_nth => //.
      exact: le_trans.
      apply: sort_sorted_fst => //.
      apply: sort_sorted => x y.
      exact: le_total.
      by rewrite inE size_map size_sort size_map (leq_trans pi)// leq_pred.
      by rewrite inE/= size_map size_sort size_map.
    have H3 : (sorted_bnds`_i).2 <= (sorted_bnds`_i.+1).2.
      have [j Hj HjE] := L3 i pi.
      have [k Hk HkE] := L4 i pi.
      rewrite -HjE -HkE !(nth_map 0)//=.
      apply: contiguous_intervals_sort' => //.
      by move: compactP; rewrite Rcompact_boundE/= => -[].
      by move: compactP; rewrite Rcompact_boundE/= => -[].
      suff: contiguous_intervals_support P p`_k by [].
      rewrite Pp/=.
      by apply/(nthP 0); exists k.
      move: H2.
      move: HjE; rewrite (nth_map 0)//=.
      move: HkE; rewrite (nth_map 0)//=.
      by move=> <- <-.
    have [j Hj HjE] := L3 i pi.
    have [k Hk HkE] := L4 i pi.
    move: H2 H3.
    rewrite -HkE -HjE.
    rewrite !(nth_map 0)//= => H2 H3.
    have [jk|jk] := eqVneq (p`_j) (p`_k); last first.
      rewrite leNgt; apply/negP => i1i.
      pose m := ((contiguous_intervals1 P p`_k) + (contiguous_intervals2 P p`_j)) / 2.
      have : m \in contiguous_intervals P p`_j `&` contiguous_intervals P p`_k.
        rewrite contiguous_ooitv//; last 2 first.
        by move: compactP; rewrite Rcompact_boundE/= => -[].
        by move: compactP; rewrite Rcompact_boundE/= => -[].
        rewrite contiguous_ooitv//; last 2 first.
        by move: compactP; rewrite Rcompact_boundE/= => -[].
        by move: compactP; rewrite Rcompact_boundE/= => -[].
        rewrite !inE/= !in_itv/=; split.
          apply/andP; split.
            by rewrite /m (le_lt_trans H2)// midf_lt//.
          by rewrite /m midf_lt//.
        apply/andP; split.
          by rewrite /m midf_lt//.
        rewrite /m.
        rewrite (lt_le_trans _ H3)//.
        by rewrite midf_lt//.
      have /trivIsetP/(_ _ _ Logic.I Logic.I jk) := @disjoint_contiguous_intervals _ P.
      move=> ->.
      by rewrite in_set0.
    move: jk => /eqP.
    rewrite nth_uniq// => /eqP jk; subst k.
    move: HjE.
    rewrite HkE.
    rewrite sorted_bndsE.
    rewrite (nth_map 0)//; last first.
      by rewrite (perm_size hsorted_bnds) size_iota size_map.
    rewrite [in X in _ = X -> _](nth_map 0); last first.
      by rewrite (perm_size hsorted_bnds) size_iota size_map.
    rewrite /unsorted_bnds/= => /eqP.
    rewrite nth_uniq; last 3 first.
      rewrite size_map.
      have : h`_i.+1 \in h.
        apply/(nthP 0); exists i.+1 => //.
        by rewrite (perm_size hsorted_bnds) size_iota size_map.
      rewrite (perm_mem hsorted_bnds) mem_iota leq0n add0n/=.
      by rewrite size_map.
      rewrite size_map.
      have : h`_i \in h.
        apply/(nthP 0); exists i => //.
        by rewrite (perm_size hsorted_bnds) size_iota size_map.
      rewrite (perm_mem hsorted_bnds) mem_iota leq0n add0n/=.
      by rewrite size_map.
      apply/(uniqP 0) => x y/=.
      rewrite !inE !size_map => xp yp Hxy.
      apply/eqP/negPn/negP => xy.
      rewrite !(nth_map 0)// in Hxy.
      have {}xy : p`_x != p`_y by rewrite (nth_uniq 0).
      have /trivIsetP/(_ _ _ Logic.I Logic.I xy) := @disjoint_contiguous_intervals _ P.
      rewrite (contiguous_ooitv); last 2 first.
        exact: (subset_has_ubound Pab).
        exact: (subset_has_lbound Pab).
      rewrite (contiguous_ooitv); last 2 first.
        exact: (subset_has_ubound Pab).
        exact: (subset_has_lbound Pab).
      case: Hxy => -> ->.
      rewrite setIid => /eqP.
      apply/negP/set0P.
      rewrite -(contiguous_ooitv); last 2 first.
        exact: (subset_has_ubound Pab).
        exact: (subset_has_lbound Pab).
      move: Pp.
      rewrite /contiguous_intervals_support/= => /(congr1 (fun x => x p`_y))/= ->.
      by apply/(nthP 0); exists y.
    have := perm_uniq hsorted_bnds.
    rewrite iota_uniq => hu.
    rewrite nth_uniq//; last 2 first.
      by rewrite (perm_size hsorted_bnds) size_iota size_map.
      by rewrite (perm_size hsorted_bnds) size_iota size_map.
    rewrite -addn1.
    rewrite -{2}(addn0 i).
    by rewrite eqn_add2l.
  - move=> i.
    rewrite prednK// ?lt0n ?size_eq0// => pi.
    have [j jp ij] := L5 _ pi.
    rewrite ij/=.
    have : P (contiguous_intervals1 P j).
      apply: mem_contiguous_intervals1 => //.
      move: Pp.
      rewrite /contiguous_intervals_support/=.
      move/(congr1 (fun x => x j)).
      by rewrite /= jp => ->.
    suff : P `<=` `[inf P, sup P].
      by move=> /[apply] /=.
    apply: (subset_trans (@sub_Rhull _ _)) => //.
    by rewrite (compact_Rhull compactP P0)//.
admit.
Admitted.

Lemma compact_mem_sup (A : set R) : compact A -> A (sup A).
Proof.
rewrite Rcompact_boundE => -[cA ubA _].
Abort.

Lemma compact_mem_inf (A : set R) : compact A -> A (inf A).
Proof.
Abort.

(*
Lemma lebesgue_measure_eq_itv_bnd (A : set R) (x y : R)
 (b0 b1 : bool) :
  (x <= y) ->
  A = [set` Interval (BSide b0 x) (BSide b1 y)] ->
  (lebesgue_measure A = (y - x)%:E)%E.
Proof.
rewrite le_eqVlt => /predU1P[->|].
  move=> ->; rewrite subrr.
  case: b0; case: b1; rewrite ?set_itvoo0 ?set_itvoc0 ?set_itvco0 ?measure0//.
  by rewrite set_itv1 lebesgue_measure_set1.
move=> xy ->.
by case: b0; case: b1; rewrite lebesgue_measure_itv lte_fin xy.
Qed.
*)

From mathcomp Require Import esum.

Section max_nngr.

Definition max_nngr := (@Order.max ring_display {nonneg R}).

(* HB.instance Definition _ := Monoid.Law.on max_nngr. *)

Lemma opA : @associative {nonneg R} max_nngr.
Admitted.

Lemma op1m : left_id (0%:nng : {nonneg R}) max_nngr.
Admitted.

Lemma opm1 : right_id (0%:nng : {nonneg R}) max_nngr.
Admitted.

HB.instance Definition _ := Monoid.isLaw.Build {nonneg R} 0%:nng
  max_nngr
   opA op1m opm1.

Lemma big_max_nngr_eq (r : seq nat) :
\big[max_nngr/0%:nng]_(i <- r) 0%:nng = 0%:nng.
Proof.
apply: big1_eq.
Abort.

End max_nngr.

Lemma completed_lebesgue_measure_eq_itv (A : set R) (x y : itv_bound R) :
  (x < y)%E ->
  A = [set` Interval x y] ->
  (mu A = ereal_of_itv_bound y - ereal_of_itv_bound x)%E.
Proof.
by move=> xy ->; rewrite completed_lebesgue_measure_itv xy.
Qed.

(* https://math.stackexchange.com/questions/520209/removing-isolated-points-to-get-a-perfect-set *)
Lemma lemma6_direct : lusinN `[a, b] H.
Proof.
apply: contrapT => nl.
(* use lemma 3 *)
have [Z [Zab cZ isoZ0 Z0 HZ]] : exists Z : set R,
    [/\ Z `<=` `[a, b], compact Z, isolated Z = set0,
        mu Z = 0 & (0%R < mu [set H x | x in Z])%E].
  (* lemma3 *)
  have := image_measure0_Lusin_nondecreasing_new ab cH ndH.
  move/contra_not => /(_ nl).
  move/existsNP=> [Z /not_implyP [Zab /not_implyP[cZ /not_implyP[isoZ0
/not_implyP[muZ0]]]]].
  move/eqP; rewrite neq_lt ltNge measure_ge0/= => muHZ_gt0.
  by exists Z.
have cHZ : compact (H @` Z).
  apply: (@continuous_compact _ _ H Z); last exact: cZ.
  exact: (continuous_subspaceW Zab).
pose c : R := inf Z.
pose d : R := sup Z.
have cd : c < d.
  apply: has_bound_not_subset1_inf_sup.
  - by exists a => ? /Zab/=; rewrite in_itv/= => /andP[].
  - by exists b => ? /Zab/=; rewrite in_itv/= => /andP[].
  move=> Z1.
  move: HZ.
  rewrite measure_gt0/= => /negP; apply; apply/eqP.
  apply: countable_lebesgue_measure0.
  apply: (@sub_countable _ _ _ Z).
    exact: card_image_le.
  exact: is_subset1_countable.
have perfectZ : perfect_set Z.
  apply/perfectP; split => //.
  exact: compact_closed.
have Z_nonempty : Z !=set0.
  apply/set0P; apply/negP => /eqP Z0'.
  by move: HZ; rewrite Z0' image_set0 measure0 ltxx.
have closedZ : closed Z by exact: compact_closed cZ.
pose supp := contiguous_intervals_support Z.
have infsupp := contiguous_infinite Zab cZ Z_nonempty Z0 perfectZ.
have countsupp : countable supp by exact: subset_card_le.
have /ppcard_eqP[/= h] := eq_card_nat countsupp infsupp.
pose h1 : {bij [set: nat] >-> supp} := h^-1%FUN.
have hh1 : {in supp, cancel h h1} by exact: funK.
have h1h : cancel h1 h by move=> x; apply: invK; rewrite inE.
have ne_cgitvs n : contiguous_intervals Z (h1 n) !=set0.
  have : supp (h1 n).
    have := @bij _ _ _ _ h1.
    by move=> [+ _ _]; exact.
  by rewrite /supp/contiguous_intervals_support/=.
pose A_ n := (contiguous_intervals1 Z (h1 n)).
pose B_ n := (contiguous_intervals2 Z (h1 n)).
pose alpha := mu (H @` Z).
have fin_alpha : alpha \is a fin_num.
  rewrite gt0_fin_numE//.
  apply: (@le_lt_trans _ _ (mu (H @` `[a, b]))).
    apply: le_outer_measure.
    exact: image_subset.
  apply: (@le_lt_trans _ _ (mu `[H a, H b])).
    apply: le_outer_measure.
    apply: continuous_nondecreasing_image_itvcc => //.
    exact: ltW.
  have [|] := ltP (H b) (H a).
    rewrite ltNge.
    by rewrite ndH ?boundl_in_itv ?boundr_in_itv ?bnd_simp//= ltW.
  rewrite le_eqVlt => /predU1P[->|HaHb].
    by rewrite set_itv1 completed_lebesgue_measureE lebesgue_measure_set1.
  rewrite completed_lebesgue_measure_itv ifT ?lte_fin//=.
  by rewrite -EFinB ltry.
pose ab_ n := sort (fun x y => x.1 <= y.1)
   [tuple (A_ i, B_ i) | i < n.+1].
pose a_ n i := (nth (d, d) (ab_ n) i).1.
pose b_ n i := (nth (d, d) (ab_ n) i).2.
have blta : forall n i, (i < n)%N -> b_ n.+1 i <= a_ n.+1 i.+1.
  (* disjoint_contiguous_intervals *)
  move=> n i ni.
  rewrite leNgt; apply/negP => aibi.
  have : `]a_ n.+1 i, b_ n.+1 i[ `&` `]a_ n.+1 i.+1, b_ n.+1 i.+1[ !=set0.
    exists ((a_ n.+1 i.+1 + b_ n.+1 i.+1) / 2).
    rewrite /a_ /b_ /ab_.
    admit.
  admit.
(*
pose sI := fun n => (sval (sorted_index_prop n)).
pose sIE := fun n => (svalP (sorted_index_prop n)).1.
pose asIE := fun n => (svalP (sorted_index_prop n)).2.
*)

(*pose b_ n := [seq nth d [tuple B_ i0 | i0 < n] i | i <- sI n].*)
(*have size_bE n : size (b_ n) = n.
  by rewrite size_map (perm_size (sIE n)) size_iota.
have sorted_b n : sorted <=%R (b_ n).
  rewrite /b_.
  apply/sortedP => i.
  rewrite size_bE => i1n.
  admit.*)
(*have : forall n i, nth d (b_ n) i <= nth d (a_ n) i.+1.
  admit.*)
(*have A_lt_B_ n : if contiguous_intervals Z n == set0 then true else A_ n < B_ n.
  case: ifPn => // Zn0.
  rewrite /A_ /B_ fine_contiguous_intervals2// fine_contiguous_intervals1//.
  rewrite has_bound_not_subset1_inf_sup//.
  - apply: has_lbound_contiguous_intervals.
    by move: cZ; rewrite Rcompact_boundE/= => -[].
  - apply: has_ubound_contiguous_intervals.
    by move: cZ; rewrite Rcompact_boundE/= => -[].
  - apply: nonempty_open_interval_not_subset1 => //.
    + exact/set0P.
    + exact: open_contiguous_intervals.
    + exact: is_interval_contiguous_intervals.*)
have lbZa : lbound Z a.
  move=> r Zr.
  have := Zab r Zr.
  by rewrite /= in_itv/= => /andP[].
have ubZb : ubound Z b.
  move=> r Zr.
  have := Zab r Zr.
  by rewrite /= in_itv/= => /andP[].
pose c_ n j := nth d (c :: [seq b_ n i | i <- iota 0 n]) j.
pose d_ n j := nth d (rcons [seq a_ n i | i <- iota 0 n] d) j.
pose lambda' n := diam_max [seq `[c_ n i, d_ n i]%classic | i <- iota 0 n.+1].
have lambda'_fin n : lambda' n \is a fin_num.
  rewrite ge0_fin_numE; last exact: diam_max_ge0.
  rewrite /lambda'/diam_max big_seq_cond; apply: bigmax_lt => //= s.
  rewrite andbT in_cons => /predU1P[->|].
    by rewrite diam_itv ltey.
  admit.
pose lambda n := fine (lambda' n).
have lambda_ge0 n : 0 <= lambda n.
  rewrite fine_ge0//.
  exact: diam_max_ge0.
have mcgitv i : mu.-cara.-measurable (contiguous_intervals Z i).
  move=> k; apply: sub_caratheodory.
  apply: open_measurable.
  exact: open_contiguous_intervals.
have spl_ex : forall n, exists k : 'I_ n.+1,
   `]A_ n.+1, B_ n.+1[ `<=` `[c_ n k, d_ n k].
  move=> n.
  admit.
set k_ := fun n => sval (cid (spl_ex n)).
set ABncdk := fun n => svalP (cid (spl_ex n)).
have ex_lambda : forall n, exists k, (k < n.+1)%N
   /\ ((lambda n)%:E = mu `[c_ n k, d_ n k])%E.
  admit.
have nilambda : nonincreasing_fun lambda.
  apply/nonincreasing_seqP => n.
  rewrite /lambda.
  rewrite /d_ /c_.
(*  rewrite big_mknat.
  have kn2 : (k_ n <= n.+2)%N.
    by rewrite ltnW// ltnS ltnW.
  rewrite (big_cat_nat_idem _ (leq0n (k_ n)) kn2)/=; last by rewrite maxxx.
  rewrite big_nat_recl; last by rewrite ltnW.
  rewrite big_nat_recl//; last by rewrite -ltnS.
  rewrite big_mknat.
  rewrite (big_cat_nat_idem _ (leq0n (k_ n)) (ltnW (ltn_ord (k_ n))))/=; last first.
    by rewrite maxxx.
  rewrite big_nat_recl//; last by rewrite -ltnS.
  apply: le_max2 => //.
    rewrite le_eqVlt; apply/orP; left; apply/eqP.
    apply: eq_big_nat => i /andP[i0 ik].
    congr `| _ - _ |.
      admit.
    admit.
  rewrite maxA.
  apply: le_max2.
    rewrite ge_max; apply/andP; split.
      admit.
    admit.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  apply: eq_big_nat => i /andP[ki iltn].
  admit.
*)
  admit.
have lambda0 : lambda @ \oo --> 0.
  apply/cvgrPdist_lt => /= e e0.
  apply/not_notP.
  rewrite /eventually/filter_from/=.
  move/forallPNP/(_ _ I) => H.
(*
  suff : ~ (forall N, exists n, (N <= n)%N /\ e <= lambda n).
    apply => N.
    have/= := H N.
    move/existsNP => [n/=/not_implyP[Nn]].
    move/negP; rewrite -leNgt sub0r normrN ger0_norm// => el.
    by exists n; split.
  move/choice => [n_ /all_and2[Nn eln]].
  have : e <= limn lambda.
    apply: limr_ge.
      apply: (nonincreasing_is_cvgn nilambda).
      by exists 0 => _ [n _ <-].
    apply: nearW.
    move=> i.
    apply: (le_trans (eln i)).
    exact: nilambda.
  move/(lt_le_trans e0).
  rewrite -lte_fin.
  apply/negP; rewrite -leNgt.
  rewrite (_ : 0%:E = 0%E)// -Z0.
  rewrite -EFin_lim; last first.
    apply: (nonincreasing_is_cvgn nilambda).
    by exists 0 => _ [n _ <-].

  have -> : (mu Z = limn (fun n => mu (`[inf Z, sup Z] `\`
      \big[setU/set0]_(i < n.+1) `]a_ n i, b_ n i[%classic)))%E.
    admit.
  apply: lee_lim.
  - admit.
  - admit.
  near=> n.
  rewrite setD_bigcup_itvoo; last 5 first.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  have [k [kn/= ->]] := ex_lambda n.
  rewrite le_outer_measure//.
  have [|k0] := leqP k 0.
    rewrite leqn0; move/eqP ->.
    move=> x /=.
    rewrite /c_ /d_ /= nth_rcons/= ifT ?nth_map_iota; last 2 first.
    - by near: n.
    - by rewrite size_map size_iota; near: n.
    by left; left.
  have [|] := leqP n k.
    rewrite leq_eqVlt => /predU1P[->|].
      case: k kn k0 => // k kn k0 x/= cdx; right.
      move: cdx.
      rewrite /c_ /d_.
      have -> : nth d (c :: [seq b_ k.+1 i | i <- iota 0 k.+1]) k.+1 =
                   nth d [seq b_ k.+1 i | i <- iota 0 k.+1] k by [].
      rewrite nth_map_iota//.
      rewrite nth_rcons ifF; last first.
        rewrite size_map size_iota ltnn//.
      rewrite size_map size_iota eq_refl.
        
      admit.
    move=> nk.
    by rewrite ltnS leqNgt nk in kn.
  case: k kn k0 => // k kn _ kltn.
  rewrite /=/ocitv_type => x/= cdx; left; right.
  rewrite -(bigcup_mkord n (fun k => `[b_ n k, a_ n k.+1]%classic)).
  exists k => //=.
  move: cdx.
  rewrite /c_ /d_ /= nth_rcons/= ifT; last by rewrite size_map size_iota.
  by rewrite !nth_map_iota.
  admit.
*)
  admit.
have nth_b_ n (i j : 'I_n) : (i <= j)%N -> b_ n i <= b_ n j.
  move=> ij.
  (*by apply: le_sorted_leq_nth => //; rewrite inE size_bE.*) admit.
have construct_x n :
  exists x : seq R, [/\ itv_partition c d (behead x),
    (mesh c d (behead x) <= lambda n),
    (forall i : 'I_ n.+1, c_ n i \in x /\ d_ n i \in x),
    (n < size x)%N &
    (forall (i j : 'I_ n.+1), nth d x j \notin `]c_ n i, d_ n i[) ].
  admit.
pose x := fun n => sval (cid (@construct_x n)).
have pcdx n : itv_partition c d (behead (x n)).
  by have [] := proj2_sig (cid (@construct_x n)).
have max_x n : mesh c d (behead (x n)) <= lambda n.
  by have [] := proj2_sig (cid (construct_x n)).
pose S_ n : R := variation c d f (behead (x n)).
pose V_ n : R := \sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)| +
     (\sum_(i < n) fine (total_variation (A_ i) (B_ i) f))%R.
pose CD_ n := merge <=%R [tuple c_ n i | i < n.+1] [tuple d_ n i | i < n.+1].
have sub_xcd n : subseq (CD_ n) (x n).
  admit.
have SV n : S_ n <= V_ n.
  rewrite /S_ /V_.
  rewrite /variation.
  rewrite /=.
  admit.
pose Vcd := fine (total_variation c d f).
have V_tv n : V_ n <= Vcd.
  admit.
have Soo_tv : S_ n @[n --> \oo] --> Vcd.
  have ac : a <= c.
    apply: lb_le_inf; last by move=> ? /Zab /=; rewrite in_itv/= => /andP[].
    apply/set0P/negP; move/eqP => Z0'.
    have := HZ; apply/negP.
    rewrite -leNgt le_eqVlt; apply/predU1P; left.
    by rewrite Z0' image_set0 measure0.
  have db : d <= b.
    apply: ge_sup; last by move=> ? /Zab /=; rewrite in_itv/= => /andP[].
    apply/set0P/negP; move/eqP => Z0'.
    have := HZ; apply/negP.
    rewrite -leNgt le_eqVlt; apply/predU1P; left.
    by rewrite Z0' image_set0 measure0.
  have cdcf : {within `[c, d], continuous f}.
    apply: continuous_subspaceW cf.
    by apply: subset_itv; rewrite bnd_simp.
  have cdbvf : bounded_variation c d f.
    apply: (bounded_variationl (ltW cd) db).
    apply: bounded_variationr ac _ bvf.
    by apply: ltW; exact: (lt_le_trans cd).
  have := lemma5 cd cdcf pcdx max_x lambda0.
  rewrite /S_ /Vcd.
  rewrite -[X in _ --> X -> _](@fineK _ (total_variation c d f)); last first.
    admit.
  by move/fine_cvgP => -[_ /=].
have Voo_V : V_ n @[n --> \oo] --> Vcd.
  apply: (squeeze_cvgr _ Soo_tv); last first.
    exact: cvg_cst.
  apply: nearW => n.
  apply/andP; split.
    exact: SV.
  exact: V_tv.
have [n0] : exists2 n0, (0 < n0)%N & forall n, (n >= n0)%N -> V_ n > Vcd - (fine alpha) / 2.
  have alpha20 : 0 < fine alpha / 2.
    rewrite divr_gt0//.
    rewrite -lte_fin fineK//.
  have := Voo_V (ball Vcd (fine alpha / 2)) (nbhsx_ballx _ _ alpha20).
  move=> [n0 _ H].
  exists n0.+1 => //n n0n.
  have := H n (ltnW n0n).
  rewrite /ball/=.
  rewrite ger0_norm; last first.
    rewrite subr_ge0.
    exact: V_tv.
  by rewrite ltrBlDl -ltrBlDr.
move=> n00.
have Z_set0 : Z !=set0.
  apply/set0P/negP; move/eqP => Z_set0.
  have := HZ.
  by rewrite Z_set0 image_set0 measure0; apply/negP; rewrite -leNgt.
near \oo => n.
have n0n : (n0 <= n)%N by near: n; exact: nbhs_infty_ge.
move/(_ n n0n).
(* (4) *)
rewrite /Vcd/V_.
have -> : fine (total_variation c d f) =
  \sum_(i < n.+1) `|H (d_ n i) - H (c_ n i)| +
   (\sum_(i < n) fine (total_variation (A_ i) (B_ i) f))%R.
  admit.
rewrite addrAC ltrD2r.
(* (5.5) (between (5) and (6)) *)
have alphaH : fine alpha < \sum_(i < n.+1) `|H (d_ n i) - H (c_ n i)|.
  rewrite /alpha.
  have -> : Z = ([set` Rhull Z] `\` cplt_hull Z).
   admit.
  rewrite setDE.
  apply: (@le_lt_trans _ _
    (fine (mu ((H @` [set` Rhull Z]) `&` (H @` (~` cplt_hull Z)))))).
    apply: fine_le.
    - admit.
    - admit.
    apply: le_outer_measure.
    exact: sub_image_setI.
  admit.
move/(@lt_trans _ _ _ (fine alpha / 2)).
rewrite ltrBrDl -splitr; move/(_ alphaH).
(* (6.5) (between (6) and (7)) *)
pose abcd (i : 'I_ n.+1) := [set k | `[A_ k, B_ k] `<=` `[c_ n i, d_ n i]].
have {}n0n : (n0 < n.+1)%N.
  admit.
set on0 := Ordinal n0n.
set Uabcdn := \bigcup_(j in abcd on0) `[A_ j, B_ j]%classic.
have cdi (i : 'I_ n.+1) : c_ n i <= d_ n i.
  admit.
have itvfcd (i : 'I_ n.+1) : is_interval (f @` `[c_ n i, d_ n i]).
  apply: (is_interval_image_cc cf).
  apply: subset_itv => //; rewrite bnd_simp.
    rewrite /c_.
    (* a <= c_ n i *)
    admit.
  rewrite /d_.
  (* d_ n i <= b *)
  admit.
have cUabcdn : closed Uabcdn.
    admit.
have hull_Uabcd (i : 'I_ n.+1) : Rhull Uabcdn = `[(c_ n i), (d_ n i)].
    admit.
have prop65 : forall i : 'I_ n.+1, (`|f (d_ n i) - f (c_ n i)|%:E <=
  \sum_(n <= j <oo | `[< `[A_ j, B_ j] `<=` Uabcdn >])
     oscillation f `[A_ j, B_ j])%E.
  move => i.
  apply: lime_ge.
    apply: ereal_nondecreasing_is_cvgn.
    apply: ereal_nondecreasing_series => k _ _.
    exact: oscillation_ge0.
  apply/nearW => k.
  have := @lemma4 _ (c_ n i) (d_ n i) (cdi i) f Uabcdn
                 (itvfcd i) cUabcdn (hull_Uabcd i).
  move/andP => [le1 le2].
  apply: (le_trans (le_trans le1 le2)).
  have -> : (mu^*%mu [set f x | x in Uabcdn] = 0)%E.
    apply/eqP; rewrite eq_le; apply/andP; split; last first.
      exact: outer_measure_ge0.
    have <- : mu^*%mu (f @` Z) = 0.
      rewrite measurable_mu_extE; last first.
        apply: sub_caratheodory.
        apply: compact_measurable.
        apply: continuous_compact => //.
        exact: continuous_subspaceW cf.
      apply: lusinf => //.
      apply: sub_caratheodory.
      exact: compact_measurable.
    apply: le_outer_measure.
    apply: image_subset.
    apply: bigcup_sub => j.
    rewrite /abcd/=.
    move/subset_trans; apply.
    rewrite /a_ /b_.
(*    apply: (subset_trans (contiguous_intervalsS _)).
    rewrite /a_.
*)
    admit.
  admit.
(* (7) *)
have : ((\sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)|)%:E <=
  \sum_(n <= i <oo) oscillation f `[A_ i, B_ i])%E.
  apply: lime_ge.
    apply: ereal_nondecreasing_is_cvgn.
    apply: ereal_nondecreasing_series => m _ _.
    exact: oscillation_ge0.
  near=> m.
  admit.
  (* have := lemma4. *)
have ifcd : is_interval (f @` `[c, d]).
  by apply: (is_interval_image_cc cf); apply: subset_itv; rewrite bnd_simp;
    [exact: lb_le_inf|exact: ge_sup].
have clZ : closed Z by exact: compact_closed.
have hZE : Rhull Z = `[c, d].
  congr Interval.
  - rewrite ifT; last by apply/asboolP; exists a.
    congr BSide.
    apply/asboolP.
    admit.
  - rewrite ifT; last by apply/asboolP; exists b.
    congr BSide.
    apply/asboolPn.
    rewrite not_notE.
    admit.
have := (@lemma4 _ _ _ (ltW cd) f Z ifcd clZ hZE).
rewrite measurable_mu_extE/=; last first.
  admit.
have -> : mu (f @` Z) = 0.
  apply: lusinf => //=.
  apply: sub_caratheodory.
  exact: compact_measurable.
rewrite add0r.
admit.
Admitted.

End lemma6_direct.

End lemma6_direct_new.

Section lemma6_converse.
Context {R : realType}.
Variables a b : R.
Hypotheses ab : a < b.

Local Notation mu := (@completed_lebesgue_measure R).

Variable f : R -> R.

Let H := fun x => fine (total_variation a ^~ f x).

(* lemma6(i) *)
Lemma total_variation_Lusin :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] H -> lusinN `[a, b] f.
Proof.
move=> cf abf.
move=> lusinNH Z Zab/= mZ mZ0.
have muZ_lty : ((wlength idfun)^*%mu Z < +oo)%E.
  move: mZ0.
  rewrite /mu/=.
  (* TODO: lemma to avoid unfold *)
  rewrite /completed_lebesgue_stieltjes_measure.
  by rewrite /completed_measure_extension => ->.
move : muZ_lty => /(@lebesgue_measure_Gdelta_approx R Z)[G [ZG oG Gnonincreasing muZ]].
pose Z1 := `]a, b[ `&` \bigcap_i G i.
suff: mu (f @` Z1) = 0.
  move=> mfZ1.
  apply/eqP; rewrite eq_le measure_ge0 andbT.
  rewrite -mfZ1.
  rewrite le_outer_measure//.
  rewrite /Z1.

  apply: image_subset.
  rewrite -bigcapIr//.
  apply: sub_bigcap => i _.
  rewrite subsetI; split => //.
  admit.
have H1 : mu (H @` Z1) = mu (\bigcap_i (H @` (G i))) /\
       mu (\bigcap_i (H @` (G i))) = 0.
  split.
    rewrite completed_lebesgue_measureE.
    have := @measure_image_nondecreasing_fun R a b H ab _ G.
    (* mismatch Z1 should be an intersection of G's... *)
    admit.

(*      rewrite fine_le//.
      + apply/bounded_variationP => //.
        exact: bounded_variationl abf.
      + apply/bounded_variationP => //.
        exact: bounded_variationl abf.
      + apply: (total_variation_nondecreasing f) => //; rewrite ?in_itv/=.
        by rewrite xa/=; exact: xb.
        by rewrite ya/=; exact: yb.
    - exact: total_variation_continuous.
    - move=> k.*)

  admit.
have H2 : mu (H @` G i) @[i --> \oo] --> 0%E.
  admit.
pose G_ i := \bigcup_j (open_disjoint_itv (oG i) j).
have H3 i :
  mu (f @` Z1) = mu (f @` (\bigcup_j (Z1 `&` (open_disjoint_itv (oG i) j)))).
  admit.
have H4 i :
    (mu (f @` (\bigcup_j (Z1 `&` (open_disjoint_itv (oG i) j)))) <=
    \sum_(j <oo) (mu^*)%mu (f @` (Z1 `&` (open_disjoint_itv (oG i) j))))%E.
  admit.
have H5 i :
    (\sum_(j <oo) (mu^*)%mu (f @` (Z1 `&` (open_disjoint_itv (oG i) j))) <
    \sum_(j <oo) oscillation f (closure (open_disjoint_itv (oG i) j)))%E.
  admit.
have H6 i :
    (\sum_(j <oo) oscillation f (closure (open_disjoint_itv (oG i) j)) =
    mu (H @` G_ i))%E.
  admit.
apply/eqP; rewrite eq_le measure_ge0 andbT.
Abort.

End lemma6_converse.
