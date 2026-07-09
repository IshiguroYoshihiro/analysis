From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_boot all_order ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import interval_inference archimedean.
From mathcomp Require Import mathcomp_extra boolp contra classical_sets functions.
From mathcomp Require Import cardinality fsbigop interval set_interval.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import real_interval esum measure.
From mathcomp Require Import lebesgue_stieltjes_measure lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import realfun exp derive borel_hierarchy.

(**md**************************************************************************)
(* # Absolute Continuity                                                      *)
(* ```                                                                        *)
(*        abs_cont a b f == the function f : R -> R is absolutely continuous  *)
(*                          over [a, b]                                       *)
(*   abs_cont_order a bf == equivalent definition of abs_cont where the       *)
(*                          (non-overlapping) intervals forming the           *)
(*                          subdivision or ordered                            *)
(*            lusinN A f == the function f : R -> R satisfies the Lusin N     *)
(*                          condition over A : set R                          *)
(*       oscillation f A == oscillation of function f : R -> R on A : set R   *)
(*                          This is an extended real number.                  *)
(* ```                                                                        *)
(* ref: An Elementary Proof of the Banach–Zarecki Theorem                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* TODO: PR? *)
Lemma setNEFin {R : realType} (f : R -> R) (A : set R) :
  [set (- x)%E | x in ((EFin \o f) @` A)] = (EFin \o (\- f)%R) @` A.
Proof.
apply/seteqP; split => [_ [_/= [r Ar] <- <-]|_/= [r Ar] <-].
  by exists r.
by exists (f r)%:E => //; exists r.
Qed.

(* TODO: PR? *)
Lemma ereal_inf_sup {R : realType} (A : set (\bar R)) : A !=set0 ->
  (ereal_inf A <= ereal_sup A)%E.
Proof.
move=> [a Aa].
by rewrite (@le_trans _ _ a)//;
  [exact: ereal_inf_lbound|exact: ereal_sup_ubound].
Qed.

Section Rbounded_closed_compact.
Context {R : realType}.

(* can be proved by bounded_closed_compact? *)
Lemma Rbounded_closed_compact (A : set R) :
  bounded_set A -> closed A -> compact A.
Proof.
move=> [M [Mreal normAltM]] Acl.
have Mnco : compact `[(- (M + 1)), (M + 1)] by exact: segment_compact.
apply: subclosed_compact Acl Mnco _ => v /normAltM normvleM.
suff : `|v| <= M + 1 by rewrite ler_norml.
by apply: le_trans (normvleM _ _); last by rewrite ltrDl.
Qed.

End Rbounded_closed_compact.

(* TODO: generalize and PR *)
Section bounded_set_lemmas.
(*
Context {K : realType}.
Context {V : normedModType K}.
 *)
Context {R : realType}.
Implicit Types (A : set R).

Lemma bounded_has_ubound A : bounded_set A -> has_ubound A.
Proof.
move=> [bnd [_ bndA]].
exists (bnd + 1) => x Ax.
apply: ler_normlW.
apply: bndA => //.
by rewrite ltrDl.
Qed.

Lemma bounded_has_lbound A : bounded_set A -> has_lbound A.
Proof.
move=> [bnd [_ bndA]].
exists (- (bnd + 1)) => x Ax.
apply: lerNnormlW.
apply: bndA => //.
by rewrite ltrDl.
Qed.

Lemma Rbounded_setE :
   @bounded_set = [set A : set R | has_lbound A /\ has_ubound A].
Proof.
rewrite eqEsubset; split => A/=.
  by move=> /[dup]/bounded_has_lbound ? /bounded_has_ubound ?; split.
move=> [[l Al] [u Au]].
exists (maxr `|u| `|l|); split => //.
move=> x ulx z Az/=.
apply/ltW.
apply: (le_lt_trans _ ulx).
rewrite ler_norml; apply/andP; split.
- suff lz : - `|l| <= z.
    rewrite /maxr; case: ifP=> // /negP/negP; rewrite -leNgt -lerN2.
    by move/le_trans; apply.
  rewrite lerNl -normrN ler_normr lerN2; apply/orP; left.
  exact: Al.
- suff zu : z <= `|u| by rewrite /maxr; case: ifP => // /ltW; apply: le_trans.
  by rewrite ler_normr; apply/orP; left; exact: Au.
Qed.

Lemma Rcompact_boundE :
  @compact R = [set A | [/\ closed A, has_ubound A & has_lbound A]].
Proof.
rewrite eqEsubset.
split.
- move=> A; split.
  + exact: compact_closed.
  + apply: bounded_has_ubound; exact: compact_bounded.
  + apply: bounded_has_lbound; exact: compact_bounded.
- move=> A [cA haslbA hasubA].
  apply: Rbounded_closed_compact => //.
  by rewrite Rbounded_setE.
Qed.

End bounded_set_lemmas.

Lemma variation_le_total_variation {R : realType} (c d : R) s g :
   itv_partition c d s -> (* maybe path <=%R c s and all (< d) s are necessary *)
   ((variation c d g s)%:E <= total_variation c d g)%E.
Proof.
move=> ps.
apply: le_ereal_sup_tmp.
exists (variation c d g s)%:E => //.
exists (variation c d g s) => //.
by exists s.
Qed.

(* TODO: PR? *)
Section open_mem_lemmas.
Context {R : realType}.
Implicit Type (A : set R).

Lemma open_haslb_memNinf A : has_lbound A -> open A ->
  ~ (A (inf A)).
Proof.
move=> haslbA oA; rewrite -{1}((interior_id A).1 oA).
by move/(left_bounded_interior haslbA); rewrite /= ltxx.
Qed.

Lemma open_hasub_memNsup A : has_ubound A -> open A ->
  ~ (A (sup A)).
Proof.
move=> hasubA oA; rewrite -{1}((interior_id A).1 oA).
by move/(right_bounded_interior hasubA); rewrite /= ltxx.
Qed.

Lemma slosed_haslb_mem_inf A : has_lbound A -> closed A ->
  A (inf A).
Proof.
move=> haslbA cA.
Abort.

End open_mem_lemmas.

Section completed_algebra_lemmas.
Context {d : measure_display}.
Context {T : semiRingOfSetsType d}.
Context {R : realType}.
Variable (mu : measure T R).
Implicit Types (A B : set T).

Lemma completed_algebra_measurable_eq_measure A B :
  d.-measurable A ->
  mu A = mu B ->
  (completed_algebra_gen mu).-sigma.-measurable B.
Proof.
move=> mA mAB.
rewrite /completed_algebra_gen/=.
rewrite /measurable/=.
rewrite /sigma_algebra/=.
Abort.

End completed_algebra_lemmas.

Section lemmas.

(* PR? *)
Lemma ball_is_interval (R : realType) (x e : R) :
  0 < e -> is_interval (ball x e).
Proof. by move=> e0; rewrite ball_itv; exact: interval_is_interval. Abort.

(* TODO:PR in topology_structure? *)
Lemma bigcap_open (R : topologicalType) (F : (set R) ^nat)  :
  (forall i, open (F i)) ->
  forall i, open (\bigcap_(j < i) F j).
Proof.
move=> HU.
elim.
  rewrite bigcap_mkord.
  rewrite big_ord0.
  exact: openT.
move=> n IH.
rewrite bigcap_mkord big_ord_recr/=.
apply: openI => //.
by rewrite -bigcap_mkord.
Qed.

(* TODO: PR *)
Lemma bigcap_cvg_mu d (T : algebraOfSetsType d) {R : realFieldType}
  (mu : {measure set T -> \bar R}) (F : (set T)^nat) :
(mu (F 0%N) < +oo)%E ->
(forall i : nat, d.-measurable (F i)) ->
d.-measurable (\bigcap_n F n) ->
(mu \o (fun n => (\bigcap_(i < n.+1) F i))) x @[x --> \oo] --> mu (\bigcap_n F n).
Proof.
move=> Foo mF mFoo.
have Hcap : \bigcap_n F n = \bigcap_n (\bigcap_(i < n.+1) F i).
  apply/seteqP; split.
    move=> x Fx n _ i ni.
    by apply: Fx.
  move=> x Fx n _.
  by apply: (Fx n) => /=.
rewrite Hcap.
apply: nonincreasing_cvg_mu.
      by rewrite bigcap_mkord big_ord1.
    move=> n.
    by apply: fin_bigcap_measurable.
  by rewrite -Hcap.
apply/nonincreasing_seqP => n.
rewrite !bigcap_mkord big_ord_recr/= subsetEset.
exact: subIsetl.
Qed.

Lemma big_nat_setUP T (n : nat) (F : nat -> _) (x : T) :
reflect (exists2 i, (i < n)%N & x \in F i) (x \in \big[setU/set0]_(0 <= i < n) F i).
Proof.
apply: (iffP idP) => [|[i Pi]]; last first.
  rewrite !inE.
  rewrite big_mkord.
  by apply: bigsetU_sup.
rewrite inE.
elim: n.
  by rewrite big_nil.
move => n IH.
rewrite big_nat_recr //=; case.
  move/IH => [k kn xFk].
  exists k => //.
  by rewrite ltnS ltnW.
move=> Fnx.
exists n => //.
by rewrite inE.
Qed.

Lemma big_ord_setUP T (n : nat) (F : 'I_n -> _) (x : T) :
reflect (exists i, x \in F i) (x \in \big[setU/set0]_(i < n) F i).
Proof.
apply: (iffP idP) => [xFi|[i xFi]]; last first.
  move: n => [[//]|n] in i F xFi *.
  have /big_nat_setUP : (exists2 i, (i < n.+1)%N & x \in (F \o inord) i).
    by exists i => //=; rewrite inord_val.
  rewrite big_mkord /=.
  by under eq_bigr do rewrite inord_val.
move: n => [|n] in F xFi *.
  by move: xFi; rewrite big_ord0 inE.
suff: exists2 i, (i < n.+1)%N & x \in F (inord i).
  move=> [i ni] xFi'.
  by exists (inord i).
apply/big_nat_setUP.
rewrite big_mkord.
by under eq_bigr do rewrite inord_val.
Qed.

(* already in sequences.v as a Let *)
Lemma near_eq_lim (R : realFieldType) (f g : nat -> \bar R) :
  cvgn g -> {near \oo, f =1 g} -> limn f = limn g.
Proof.
move=> cg fg; suff: f @ \oo --> limn g by exact/cvg_lim.
by apply: cvg_trans cg; apply: near_eq_cvg; near do apply/esym.
Unshelve. all: by end_near. Qed.

(* already in sequences.v as a Let *)
Lemma lim_shift_cst (R : realFieldType) (u : (\bar R) ^nat) (l : \bar R) :
    cvgn u -> (forall n, 0 <= u n)%E -> (-oo < l)%E ->
  limn (fun x => l + u x) = l + limn u.
Proof.
move=> cu u0 hl; apply/cvg_lim => //; apply: cvgeD (cu); last first.
  exact: cvg_cst.
rewrite ltninfty_adde_def// inE (@lt_le_trans _ _ 0%E)//.
by apply: lime_ge => //; exact: nearW.
Qed.

(* NB: not used *)
Lemma near_at_right_in_itv {R : realFieldType} [a b : R] :
  {in `[a, b[, forall y, \forall x \near y^'+, x \in `]a, b[}.
Proof.
move=> x; rewrite in_itv/= => /andP[ax xb].
near=> y; rewrite in_itv/=; apply/andP; split => //.
by rewrite (le_lt_trans ax).
Unshelve. all: by end_near. Qed.

Lemma near_at_left_in_itv {R : realFieldType} [a b : R] :
  {in `]a, b], forall y, \forall x \near y^'-, x \in `]a, b[}.
Proof.
Abort.

End lemmas.

Section move_to_realfun.
Context {R : realType}.

(* move to realfun.v? *)
Lemma continuous_increasing_image_itvoo (a b : R) (f : R -> R) :
  {within `[a, b] , continuous f} ->
  {in `]a, b[ &, {homo f : x y / (x < y)%O}} ->
  f @` `]a, b[%classic `<=` `]f a, f b[%classic.
Proof.
move=> cf ndf.
move=> _ /= [r + <-].
rewrite in_itv /= => /andP [ar rb].
move: cf.
move/continuous_within_itvP.
move/(_ (lt_trans ar rb)) => [cf fa fb].

move : fa.
move/cvg_at_rightP.
move/(_ (fun n => a + 2^-1 ^ n.+1)).
have H : ((forall n : nat, a < (a + 2^-1 ^ n.+1)) /\ (a + 2^-1 ^ n.+1) @[n --> \oo] --> a).
  admit.
move/(_ H) => {H}.
have H : (f (a + 2^-1 ^ n.+1) - f a) @[n --> \oo] --> (0:R)%R.
  admit.
move=> cvgfa.
have : \forall x \near a^'+, f x < f r.
  admit.
rewrite -nbhs_nearE.
move=> [e /= e0].
(* move/(cvg_lim (@Rhausdorff R)). *)

(* apply: have_near. *)

(*   apply (real_cvgr_lt ). *)

(*   apply: filter_near_of. *)
(*   rewrite near_filter_onE. *)
(*   rewrite /lim. *)
(*   Unset Printing Notations. *)

(*   have : cvg (f x @[x --> a^']). *)
(*   Unset Printing Notations. *)

(*   apply: limr_le. *)
(*   - apply/cvg_ex. *)
(*     exists (f a). *)
(*     exact: fa. *)
(*   - near=> a0. *)
(*     apply: ndf. *)
(*     rewrite in_itv/=; apply/andP; split => //. *)
(*     rewrite (le_lt_trans _ rb)//. *)
(*     near: a0. *)
(*     by apply: nbhs_right_le. *)
(*     by rewrite in_itv/= ar. *)
(*     near: a0. *)
(*     by apply: nbhs_right_le. *)
(* move: (fb) => /cvg_lim <-//. *)
(* apply: limr_ge. *)
(* - apply/cvg_ex. *)
(*   exists (f b). *)
(*   exact: fb. *)
(* - near=> b0. *)
(*   apply: ndf. *)
(*   by rewrite in_itv/= ar. *)
(*   rewrite in_itv/=; apply/andP; split => //. *)
(*   by rewrite (lt_trans ar)//. *)
(*   near: b0. *)
(*   by apply: nbhs_left_ge. *)
(* Unshelve. all: by end_near. Qed. *)
(* case : (leP a b) => [|ba]. *)
(*   rewrite le_eqVlt. *)
(*   case/orP. *)
(*     by move/eqP ->; rewrite !set_itvoo0 image_set0 => _ _. *)
(*   move=> ltab cf ndf. *)
Abort.

Lemma continuous_nondecreasing_image_itvoo (a b : R) (f : R -> R) :
  {within `[a, b], continuous f} ->
  {in `]a, b[ &, {homo f : x y / (x <= y)%O}} ->
  f @` `]a, b[%classic `<=` `[f a, f b]%classic.
Proof.
move=> cf ndf x/= [r rab] <-{x}.
move: rab; rewrite in_itv/= => /andP[ar rb].
have [cabf fa fb] := (continuous_within_itvP f (lt_trans ar rb)).1 cf.
rewrite in_itv/=; apply/andP; split.
  move: (fa) => /cvg_lim <-; last exact: Rhausdorff.
  apply: limr_le.
  - apply/cvg_ex; exists (f a).
    exact: fa.
  - near=> a0.
    apply: ndf.
    + rewrite in_itv/=; apply/andP; split => //.
      rewrite (le_lt_trans _ rb)//.
      by near: a0; exact: nbhs_right_le.
    + by rewrite in_itv/= ar.
    + by near: a0; apply: nbhs_right_le.
move: (fb) => /cvg_lim <-; last exact: Rhausdorff.
apply: limr_ge.
- apply/cvg_ex; exists (f b).
  exact: fb.
- near=> b0.
  apply: ndf.
  + by rewrite in_itv/= ar.
  + rewrite in_itv/=; apply/andP; split => //.
    by rewrite (lt_trans ar).
  + by near: b0; apply: nbhs_left_ge.
Unshelve. all: by end_near. Qed.

Lemma continuous_nondecreasing_image_itvcc (a b : R) (f : R -> R) :
  a <= b ->
  {within `[a, b], continuous f} ->
  {in `[a, b] &, {homo f : x y / (x <= y)%O}} ->
  f @` `[a, b] `<=` `[f a, f b]%classic.
Proof.
move=> ab cf ndf x/= [r +] <-{x}.
rewrite in_itv/= => /andP[].
rewrite le_eqVlt => /predU1P[ar rb|ar].
  by rewrite in_itv/= ar lexx/= ndf// ?in_itv/= ar lexx ?andbT.
rewrite le_eqVlt => /predU1P[rb|rb].
  by rewrite in_itv/= rb lexx/= ndf// ?in_itv//= lexx ?andbT.
apply: continuous_nondecreasing_image_itvoo => //.
  by move=> x y xab yab; apply: ndf => //; apply: subset_itv_oo_cc.
by exists r => //=; rewrite in_itv/= ar.
Qed.

Lemma nondecreasing_fun_decomp (a b : R) (f : R -> R) :
  {in `]a, b[ &, {homo f : x y / x <= y}} ->
  forall x, x \in `]a, b[ ->
 (\forall y & z \near x, y < z -> f y < f z)
 \/ (\forall y \near x, f y = cst (f x) y).
Proof.
move=> ndf x.
rewrite in_itv/= => /andP[ax xb].
have [cstx|cstx] := pselect (\forall y \near x, f y = cst (f x) y).
  by right; apply: filterS cstx.
Abort.

Lemma nondecreasing_bound_le (a : R) (b : itv_bound R) (f : R -> R) :
  ((BLeft a) < b)%O ->
  {in (Interval (BLeft a) b) &, {homo f : x y / (x <= y)%O}} ->
  f x @[x --> a^'+] --> f a ->
  forall x, a < x -> f a <= f x.
Proof.
case: b => t b.
wlog -> : t / t = false.
  move/(_ false (Logic.eq_refl false)).
Abort.

Lemma continuous_in_nondecreasing_oo_cc (a b : R) (f : R -> R) : a < b ->
  {within `[a, b] , continuous f} ->
  {in `]a, b[ &, {homo f : x y / (x <= y)%O}} ->
  {in `[a, b] &, {homo f : x y / (x <= y)%O}}.
Proof.
move=> ab cf ndf.
have [cf' fxa fxb] := (continuous_within_itvP f ab).1 cf.
move=> r x.
rewrite !in_itv/=.
have faz z : a < z -> z <= b -> f a <= f z.
  move=> az zb.
  move : (fxa) => /cvg_lim => <-; last first.
    exact: Rhausdorff.
    apply: limr_le.
    by apply: cvgP fxa.
  near=> y.
  have yab : y \in `]a, b[ by rewrite in_itv/=; apply/andP.
  move: zb; rewrite le_eqVlt; move/predU1P => [-> |zb].
    move: (fxb) => /cvg_lim <-; last exact: Rhausdorff.
    apply: limr_ge.
      by apply: cvgP fxb.
    near=> b0.
    have b0ab : b0 \in `]a, b[ by rewrite in_itv/=; apply/andP.
    apply: ndf => //.
    by near: b0; apply: nbhs_left_ge.
  apply: ndf => //.
    by rewrite in_itv/= az zb.
  by near: y; apply: nbhs_right_le.
have fzb z : a < z -> z < b -> f z <= f b.
  move=> az zb.
  move: (fxb) => /cvg_lim <-; last exact: Rhausdorff.
  apply: limr_ge.
    by apply: cvgP fxb.
  near=> y.
  have yab : y \in `]a, b[ by rewrite in_itv/=; apply/andP.
  apply: ndf => //; first by rewrite ?in_itv/=; apply/andP.
  by near: y; apply: nbhs_left_ge.
move => /andP[]; rewrite le_eqVlt => /predU1P[<- |].
  move=> _ /andP[_]; rewrite le_eqVlt => /predU1P[-> _|xb].
    exact: faz.
  rewrite le_eqVlt => /predU1P[-> //| ax].
  by apply: faz; rewrite ?ltW.
move=> ar _ /andP[_]; rewrite 2!le_eqVlt=> /predU1P[-> |xb] /predU1P[-> |rx]//.
  by apply: fzb.
have ax : a < x by apply: lt_trans rx.
have rb : r < b by apply: lt_trans xb.
by apply: ndf => //; rewrite ?ltW ?in_itv/= ?ar ?ax.
Unshelve. all: by end_near. Qed.

Lemma continuous_nondecreasing_image_itvoo_itv (a b : R) (f : R -> R) : a < b ->
  {within `[a, b] , continuous f} ->
  {in `]a, b[ &, {homo f : x y / (x <= y)%O}} ->
  exists b0 b1,
    f @` `]a, b[%classic =
    [set x | x \in Interval (BSide b0 (f a)) (BSide b1 (f b))].
Proof.
move=> ab cf ndf.
have ndfcc := continuous_in_nondecreasing_oo_cc ab cf ndf.
have [cf' fxa fxb] := (continuous_within_itvP f ab).1 cf.
have lefab y : f a <= y -> y <= f b -> minr (f a) (f b) <= y <= maxr (f a) (f b).
  by move=> fax xfb; rewrite ge_min fax /= le_max xfb orbT.
have ge_fa x : a < x -> x < b -> f a <= f x.
  by move=> ax xb; apply: ndfcc;  rewrite ?in_itv/= ?lexx ?ltW.
have le_fb x : a < x -> x < b -> f x <= f b.
  by move=> ax xb; apply: ndfcc;  rewrite ?in_itv/= ?lexx ?ltW.
have Hfa : (\forall x \near a^'+, f x = f a)
      <-> exists2 x : R, x \in `]a, b[ & f x = f a.
  split; [move=> fa|move=> [r /[dup]rab + fra]; rewrite in_itv/= => /andP[ra _]].
    near a^'+ => a0.
    exists a0; first by rewrite in_itv/=; apply/andP.
    by near: a0; apply: filterS fa => ? ->.
  near=> a0.
  apply/eqP; rewrite eq_le; apply/andP; split; last exact: ge_fa.
  rewrite -fra.
  apply: ndf => //; first by rewrite in_itv/=; apply/andP.
  by near: a0; apply: nbhs_right_le.
have Hfb: (\forall x \near b^'-, f x = f b)
    <-> exists2 x : R, x \in `]a, b[ & f x = f b.
  split; [move=> fb|move=> [r /[dup]rab + frb]; rewrite in_itv/= => /andP[_ rb]].
    near b^'- => b0.
    exists b0; first by rewrite in_itv/=; apply/andP.
    by near: b0; apply: filterS fb => ? ->.
  near=> b0.
  apply/eqP; rewrite eq_le ; apply/andP; split; first by apply: le_fb.
  rewrite -frb.
  apply: ndf => //; first by rewrite ?in_itv/=; exact/andP.
  by near: b0; apply: nbhs_left_ge.
have [fa|fa] := pselect (\forall x \near a^'+, f x = f a).
  have [fb|fb] := pselect (\forall x \near b^'-, f x = f b).
  - exists true, false; apply/seteqP; split => [x/=|y].
        move=> [r]; rewrite in_itv/= => /andP[ar rb] <-{x}.
        by rewrite in_itv/=; apply/andP; split; [apply: ge_fa|apply: le_fb].
      rewrite /= in_itv/= => /andP[fay yfb].
      have [r] := (IVT (ltW ab) cf (lefab y fay yfb)).
      rewrite in_itv => /= /andP[].
      rewrite !le_eqVlt => /predU1P[<-{r} _ {fay} <- |ar /predU1P[/[swap] <- -> |rb <-]];
      [exact/Hfa
      |exact/Hfb
      |by exists r; rewrite // in_itv/= ar rb].
  - exists true, true; apply/seteqP; split => [x/=|y].
        move=> [r /[dup]rab]; rewrite in_itv/= => /andP[ar rb] <-{x}.
        rewrite in_itv/=; apply/andP; split; first exact: ge_fa.
        rewrite lt_neqAle; apply/andP; split; last exact: le_fb.
        apply/negP => /eqP fyb.
        move/Hfb : fb; apply.
        by exists r.
      rewrite /= in_itv/= => /andP[fay yfb].
      have [r] := (IVT (ltW ab) cf (lefab y fay (ltW yfb))).
      rewrite in_itv => /= /andP[].
      rewrite !le_eqVlt => /predU1P[<- _ {fay} <- |ar /predU1P[rb frx|rb fxr]];
      [exact/Hfa
      |by subst y r; rewrite ltxx in yfb
      |by exists r; rewrite // in_itv/= ar rb].
  have [fb|fb] := pselect (\forall x \near b^'-, f x = f b).
  - exists false; exists false; apply/seteqP; split => [x/=|y].
      move=> [r /[dup]rab +]; rewrite in_itv/= => /andP[ar rb] <-{x}.
      rewrite in_itv/=; apply/andP; split; last exact: le_fb.
        rewrite lt_neqAle; apply/andP; split; last exact: ge_fa.
        apply/negP => /eqP far.
        move/Hfa : fa; apply.
        by exists r.
      rewrite /=in_itv/= => /andP[fay yfb].
      have [r] := (IVT (ltW ab) cf (lefab y (ltW fay) yfb)).
      rewrite in_itv => /= /andP[].
      rewrite !le_eqVlt; move/predU1P => [ar _ frx|ar /predU1P[-> <- |rb <-]];
      [by subst y r; rewrite ltxx in fay
      |exact/Hfb
      |by exists r; rewrite // in_itv/= ar rb].
  - exists false; exists true.
      rewrite eqEsubset; split => [|y].
        move=> _ /= [x /[dup]xab + <-]; rewrite in_itv/= => /andP[ax xb].
        rewrite in_itv/=; apply/andP; split.
          rewrite lt_neqAle; apply/andP; split; last exact: ge_fa.
          apply/negP => /eqP fafx.
          move/Hfa : fa; apply.
          by exists x.
        rewrite lt_neqAle; apply/andP; split; last exact: le_fb.
        apply/negP => /eqP fxfb.
        move/Hfb : fb; apply.
        by exists x.
      rewrite /= in_itv/= => /andP[fay yfb].
      have [r] := (IVT (ltW ab) cf (lefab y (ltW fay) (ltW yfb))).
      rewrite in_itv => /= /andP[].
      rewrite !le_eqVlt => /predU1P[<-{r} _ faeqy|ar /predU1P[rb freqy|rb <-]];
      [by rewrite faeqy ltxx in fay
      |by subst r y; rewrite ltxx in yfb
      |by exists r; rewrite // in_itv/= ar rb].
Unshelve. all: by end_near. Qed.

(* name? *)
(* why "integral" is in name in spite of not using integral *)
Lemma integral_continuous_nondecreasing_itv (a b : R) (f : R -> R) :
  a < b ->
  {within `[a, b], continuous f} ->
  {in `]a, b[ &, {homo f : x y / (x <= y)%O}} ->
  lebesgue_measure (f @` `]a, b[) = ((f b)%:E - (f a)%:E)%E.
Proof.
move=> ab cf ndf.
have := (continuous_nondecreasing_image_itvoo_itv ab cf ndf).
have ndfcc := (continuous_in_nondecreasing_oo_cc ab cf ndf).
move=> [b0 [b1]] ->.
rewrite lebesgue_measure_itv /=.
have: f a <= f b.
  by rewrite ndfcc ?in_itv/= ?lexx ?ltW.
rewrite le_eqVlt.
move/orP; case; rewrite lte_fin; [move/eqP|]; move=> -> //.
by rewrite ltxx -EFinD subrr.
Qed.

Lemma continuous_image_segment (a b : R) (f : R -> R) :
  a <= b ->
  {within `[a, b], continuous f} ->
  exists c d, [/\ c \in `[a, b]%classic, d \in `[a, b]%classic,
     f @` `[a, b] = `[f c, f d]%classic &
    lebesgue_measure (f @` `[a, b]) = (f d - f c)%:E].
Proof.
move=> ab cf.
have ab0 : `[a, b] !=set0 by exists a => /=; rewrite boundl_in_itv.
have cpt_ab : compact `[a, b] by exact: segment_compact.
have [/= c /[dup]cab + minc] := compact_EVT_min ab0 cpt_ab cf.
rewrite inE/= in_itv/= => /andP[ac cb].
have [/= d /[dup]dab + maxd] := compact_EVT_max ab0 cpt_ab cf.
rewrite inE/= in_itv/= => /andP[ad db].
have fcfd : f c <= f d by exact: minc.
have -> : [set f x | x in `[a, b]] = `[f c, f d]%classic.
  rewrite eqEsubset; split => y.
    move=> [x xab <-]/=; rewrite in_itv/=; apply/andP; split.
      by apply: minc; rewrite inE.
    by apply: maxd; rewrite inE.
  move=> yfcfd.
  have le_y : minr (f c) (f d) <= y <= maxr (f c) (f d).
    by rewrite minEle maxEle !ifT//.
  have /orP[cd|dc] := le_total c d.
    have cfcd : {within `[c, d], continuous f}.
      apply: continuous_subspaceW cf.
      by apply: subset_itv; rewrite bnd_simp.
    have [x xcd <-] := IVT cd cfcd le_y.
    exists x => //=.
    by apply: subset_itv xcd; rewrite bnd_simp.
  have cfdc : {within `[d, c], continuous f}.
    apply: continuous_subspaceW cf.
    by apply: subset_itv; rewrite bnd_simp.
  rewrite minC maxC in le_y.
  have [x xcd <-] := IVT dc cfdc le_y.
  exists x => //=.
  by apply: subset_itv xcd; rewrite bnd_simp.
exists c, d; split => //.
rewrite lebesgue_measure_itv.
move: fcfd; rewrite le_eqVlt => /predU1P[<-|fcfd].
  by rewrite subrr ifF.
by rewrite ifT.
Qed.

End move_to_realfun.

(* TODO: PR ここから *)
(* TODO: generalize for PR? *)

Section closure_neitv_ereal.
Context {R : realFieldType}.
Implicit Types a b : \bar R.
Local Open Scope ereal_scope.

(* maybe PR#1848 *)
Lemma closure_eneitv_oo a b : a < b ->
  closure `]a, b[%classic = `[a, b]%classic.
Proof.
Admitted.

End closure_neitv_ereal.

Section closure_neitv_real.
Context {R : realType}.
Implicit Type a b : R.

Lemma closure_neitv_oo a b : a < b ->
  closure `]a, b[%classic = `[a, b]%classic.
Proof.
move=> ab.
set c := (a + b) / 2%:R.
set d := (b - a) / 2%:R.
rewrite (_:a = c - d); last by rewrite /c/d !mulrDl addrKA mulNr opprK -splitr.
rewrite (_:b = c + d); last by rewrite addrC /c/d !mulrDl mulNr subrKA -splitr.
rewrite -ball_itv -closed_ball_itv ?closure_ballE//.
apply: divr_gt0 => //.
by rewrite subr_gt0.
Qed.

Lemma closure_neitv_oc a b : a < b ->
  closure `]a, b]%classic = `[a, b]%classic.
Proof.
move=> ab.
rewrite eqEsubset; split.
  rewrite (closure_id `[a, b]%classic).1; last first.
    rewrite -closure_neitv_oo//.
    exact: closed_closure.
  exact/closureS/subset_itv_oc_cc.
rewrite -closure_neitv_oo//.
exact/closureS/subset_itv_oo_oc.
Qed.

Lemma closure_neitv_co a b : a < b ->
  closure `[a, b[%classic = `[a, b]%classic.
Proof.
move=> ab.
rewrite eqEsubset; split.
  rewrite (closure_id `[a, b]%classic).1; last first.
    rewrite -closure_neitv_oo//.
    exact: closed_closure.
  by apply: closureS; exact: subset_itv_co_cc.
rewrite -closure_neitv_oo//.
by apply: closureS; exact: subset_itv_oo_co.
Qed.

Lemma closure_neitv_cc a b : a < b ->
  closure `[a, b]%classic = `[a, b]%classic.
Proof.
symmetry; apply/closure_id; rewrite -closure_neitv_oo//.
exact: closed_closure.
Qed.

Lemma closure_neitv_bnd a b (x y : bool) : a < b ->
  closure [set` (Interval (BSide x a) (BSide y b))] = `[a, b]%classic.
Proof.
move=> ab.
case: x; case: y.
- exact: closure_neitv_co.
- exact: closure_neitv_cc.
- exact: closure_neitv_oo.
- exact: closure_neitv_oc.
Qed.

Lemma closure_neitv_rray (a : R) :
  closure `]a, +oo[%classic = `[a, +oo[%classic.
Proof.
set x := a + 1.
have -> : (`]a, +oo[ = `]a, x[ `|` `[x, +oo[)%classic.
  by apply: itv_bndbnd_setU => //; rewrite bnd_simp ltrDl.
rewrite closureU -((closure_id _).1 (@rray_closed _ _ _)).
rewrite closure_neitv_oo; last by rewrite ltrDl.
rewrite -(setUitv1 true) ?bnd_simp; last by rewrite lerDl.
rewrite -setUA [[set x] `|` _]setUidr; last first.
  by rewrite -set_itv1; apply: subset_itvl.
apply/esym.
by apply: itv_bndbnd_setU => //; rewrite bnd_simp lerDl.
Qed.

Lemma closure_neitv_lray (a : R) :
  closure `]-oo, a[%classic = `]-oo, a]%classic.
Proof.
set x := a - 1.
have -> : (`]-oo, a[ = `]-oo, x] `|` `]x, a[)%classic.
  by apply: itv_bndbnd_setU => //; rewrite bnd_simp gtrBl.
rewrite closureU -((closure_id _).1 (@lray_closed _ _ _)).
rewrite closure_neitv_oo; last by rewrite gtrBl.
rewrite -(setU1itv false) ?bnd_simp//; last by rewrite gerBl.
rewrite setUA [_ `|` [set x]]setUidl; last first.
  by rewrite -set_itv1; apply: subset_itvr.
apply/esym.
by apply: itv_bndbnd_setU => //; rewrite bnd_simp gerBl.
Qed.

(*
Lemma closure_neitv (i : interval R) :
  closure [set` i] = (* ? *)
*)

End closure_neitv_real.

Section subset_neitv.
Context {R : realType}.
Implicit Type (a b : R).

Lemma subset_neitv_oocc a b c d : a < b ->
  `]a, b[ `<=` `[c, d] ->
  `[a, b] `<=` `[c, d].
Proof.
move=> ab /closureS.
rewrite -(closure_id `[c, d]%classic).1; last first.
  exact: interval_closed.
apply: subset_trans.
by rewrite closure_neitv_oo.
Qed.

End subset_neitv.
(* TODO: PR ここまで *)

Section measurable_squeeze.
Context {R : realType}.

Lemma measure_squeeze_measurable (B A C : set R) :
  measurable A ->
  measurable C ->
  (*lebesgue_measure A = lebesgue_measure C -> NB: unused *)
  countable (C `\` A) ->
  A `<=` B -> B `<=` C -> measurable B.
Proof.
move=> mA mC cCA AB BC.
rewrite -(setDUK AB).
apply: measurableU => //.
apply: countable_measurable => //.
apply: sub_countable cCA.
apply: subset_card_le.
by apply: setSD.
Qed.

End measurable_squeeze.

Section inf_sup_lemmas.

Lemma has_bound_not_subset1_inf_sup {R : realType} (S : set R) :
  has_lbound S -> has_ubound S -> ~ (is_subset1 S) ->
  inf S < sup S.
Proof.
move=> hlS hbS.
move=> /existsNP[x] /existsNP[y] /not_implyP[Sx] /not_implyP[Sy] /eqP xy.
wlog : x y Sx Sy xy / x < y.
  move=> wlg; move: xy; rewrite neq_lt => /orP[xy|yx].
    by apply: (wlg _ _ Sx Sy) => //; rewrite lt_eqF.
  by apply: (wlg _ _ Sy Sx) => //; rewrite lt_eqF.
move=> {}xy; apply: (@le_lt_trans _ _ x).
  rewrite -(inf1 x); apply: inf_le; last 2 first.
      by exists x.
    by split => //; exists x.
  move=> _ /= [_ -> <-].
  by exists (- x); split => //=; exists x.
apply: (@lt_le_trans _ _ y) => //.
rewrite -(sup1 y); apply: sup_le; last 2 first.
    by exists y.
  by split=> //; exists y.
rewrite sub1set.
rewrite inE.
by exists y.
Qed.

End inf_sup_lemmas.

Section not_subset1P.

Lemma not_subset1P {R : realType} (D : set R) (F : {fun D >-> [set: R]}) z :
  ~ is_subset1 (D `&` F @^-1` [set z]) <->
  (exists x y, [/\ x != y, D x, D y, F x = z & F y = z]).
Proof.
split.
  move=> /existsNP[x] /existsNP[y].
  move=> /not_implyP[[/= abx /= FxFr]] /not_implyP[[aby /= FyFr]] /eqP xy.
  by exists x, y.
move=> [x [y [xy xab yab FxFr FyFr]]].
apply/existsNP; exists x; apply/existsNP; exists y.
by apply/not_implyP; split => //; apply/not_implyP; split => //; exact/eqP.
Qed.

End not_subset1P.

From mathcomp Require Import rat.

(* unused *)
Section locally_finite.
Context {T : topologicalType}.

(* https://proofwiki.org/wiki/Definition:Locally_Finite_Set_of_Subsets *)
Definition restr_sets (F : set (set T)) (U : set T) :=
     [set A | F A /\ A `&` U !=set0].

Definition locally_finite :=
  [set F : (set (set T)) | forall x : T, exists U : set T, nbhs x U /\
     finite_set (restr_sets F U)].

Let open_disj_set (F : set (set T)) :=
   [set U | open U /\ finite_set (restr_sets F U)].

(* https://proofwiki.org/wiki/
     Open_Set_Disjoint_from_Set_is_Disjoint_from_Closure *)
(* for closures_locally_finite *)
Lemma disj_set_closure (A B : set T) :
  open B -> [disjoint A & B] -> [disjoint (closure A) & B].
Proof.
move=> oB disjAB.
apply/disj_setPLR.
rewrite (closure_id (~` B)).1; last first.
  by rewrite closedC.
by apply: closureS; exact/disj_setPLR.
Qed.

Lemma closure_image_restr_setsE (F : set (set T)) (U : set T) :
  open U ->
  restr_sets (closure @` F) U = closure @` (restr_sets F U).
Proof.
move=> oU.
rewrite eqEsubset; split.
- move=> Y [[X FX cXY] /set0P/negP YU0].
  exists X => //.
  split => //.
  apply/set0P/negP.
  move/eqP/disj_set2P/(disj_set_closure oU)/disj_set2P/eqP.
  by rewrite cXY.
- move=> Y [X [Fx [x [Xx Ux]] cXY]].
  split.
  by rewrite -cXY; exists X.
  exists x; split => //.
  rewrite -cXY.
  exact: subset_closure.
Qed.

Lemma restr_sets_subset (F : set (set T)) (A B : set T) :
  A `<=` B -> restr_sets F A `<=` restr_sets F B.
Proof.
move=> AB X [FX XA0].
split => //.
apply: (@subset_nonempty _ (X `&` A)) => //.
exact: setIS.
Qed.

Lemma restr_sets_subset_finite_set (F : set (set T)) (A B : set T) :
  A `<=` B -> finite_set (restr_sets F B) -> finite_set (restr_sets F A).
Proof.
move=> AB.
apply: sub_finite_set.
exact: restr_sets_subset.
Qed.

(* https://proofwiki.org/wiki/
     Closures_of_Elements_of_Locally_Finite_Set_is_Locally_Finite *)
(* for closed_locally_finite_bigcup_closed *)
Lemma closures_locally_finite (F : set (set T)) :
  locally_finite F ->
    locally_finite (closure @` F).
Proof.
move=> lF.
set BB := [set B | exists A, A \in F /\ B = closure A].
move=> x.
have [U [Ux finFU]]:= lF x.
exists (interior U); split=> //.
  exact: nbhs_interior.
rewrite closure_image_restr_setsE//; last exact: open_interior.
apply: finite_image.
apply: restr_sets_subset_finite_set finFU.
exact: interior_subset.
Qed.

Definition open_coverT :=
  [set F : set (set T) |
      (forall A, F A -> open A) /\ (\bigcup_(A in F) A = [set: T])].

Lemma open_coverTP (F : set (set T)) : open_coverT F <->
  ((forall A, F A -> open A) /\ (forall x : T, exists A, F A /\ A x)).
Proof.
split => -[H1 H2].
- split => //.
  move=> x.
  have : [set: T] x by [].
  rewrite -H2 => -[A FA Ax].
  by exists A; split.
- split => //.
  rewrite eqEsubset; split => x//= _.
  have [A [FA Ax]] := H2 x.
  by exists A.
Qed.

Lemma open_coverT_open (F : set (set T)) A : open_coverT F ->
  F A -> open A.
Proof. move=> [+ _]; exact. Qed.

Lemma open_coverT_coverT (F : set (set T)) : open_coverT F ->
  \bigcup_(A in F) A = [set: T].
Proof. by move=> [_ +]. Qed.

Lemma open_coverT_point (F : set (set T)) : open_coverT F ->
(forall x : T, exists A, F A /\ A x).
Proof. by move/open_coverTP=> [_ +]. Qed.

(* https://proofwiki.org/wiki/Characterization_of_Open_Set_by_Open_Cover *)
Lemma open_open_coverT_subspace (F : set (set T)) E :
  open_coverT F ->
  open E <-> (forall U, F U -> (@open (subspace U) E)).
Proof.
move=> ocF.
split.
- move=> oE U FU.
  have oU : open U by exact: (@open_coverT_open F).
  rewrite -open_setIS//.
  exact: openI => //.
- move=> oF.
  have {}oF : forall U : set T, F U -> (@open T (E `&` U)).
    move=> U FU.
    rewrite open_setIS//.
      exact: oF.
    exact: (@open_coverT_open F).
  rewrite -(setIT E).
  rewrite -(open_coverT_coverT ocF).
  rewrite setI_bigcupr.
  apply: bigcup_open => U FU.
  exact: oF.
Qed.

(* https://proofwiki.org/wiki/Characterization_of_Closed_Set_by_Open_Cover *)
Lemma closed_open_coverT_subspace (F : set (set T)) E :
  open_coverT F ->
  closed E <-> (forall U, F U -> (@closed (subspace U) E)).
Proof.
move=> ocF; split=> [cE|cEU].
- move=> U FU.
  have oU : open U.
    move: ocF.
      rewrite /open_coverT/= => -[].
      by move/(_ U FU).
  rewrite -openC.
  rewrite -open_setIS => //.
  apply: openI => //.
  by rewrite openC.
- rewrite -openC.
  apply/(open_open_coverT_subspace _ ocF).
  move=> U FU.
  rewrite openC.
  exact: cEU.
Qed.

Lemma restr_sets_bigcupIl (F : set (set T)) (U : set T) :
 \bigcup_(A in F) (U `&` A) = \bigcup_(A in (restr_sets F U)) (U `&` A).
Proof.
rewrite (bigcupID (restr_sets F U) _ F) -[RHS]setU0; congr setU => //.
  by rewrite (setIidr _)//; move=> ?[].
apply: bigcup0 => A.
rewrite /restr_sets/= => -[FA ].
rewrite -implypN => /(_ FA).
move/set0P/negP/negbNE/eqP.
by rewrite setIC.
Qed.

Section closed_locally_finite_bigcup_closed.

Arguments open : clear implicits.
Arguments closed : clear implicits.

Lemma closed_subspaceTI (A U: set T) :
closed (subspace A) U = closed (subspace A) (A `&` U).
Proof.
apply: propext.
split=> cAU.
- apply: closedI => //.
  exact: closed_subspaceT.
- rewrite -{1}(setTI U).
  rewrite -(setUv A).
  rewrite setIUl.
  apply: closedU => //.
  rewrite -openC.
  rewrite setCI setCK.
  rewrite -(setUIDK (A `|` ~` U) A).
  apply: openU.
  + rewrite setUK.
    exact: open_subspaceT.
  + rewrite setDUD setDv set0U.
    apply: open_subspace_out.
    exact: subDsetr.
Qed.

(* https://proofwiki.org/wiki/
     Union_of_Closed_Locally_Finite_Set_of_Subsets_is_Closed *)
Lemma closed_locally_finite_bigcup_closed (F : set (set T)) :
  locally_finite F ->
  (forall A : set T, F A -> closed T A) ->
  closed T (\bigcup_(A in F) A).
Proof.
move=> lF clF.
set UU := open_disj_set F.
have cover_UU : open_coverT UU.
  apply/open_coverTP.
  split; first by move=> + [].
  move=> x.
  have [A [+ finFA]] := lF x.
  rewrite nbhsE/= => -[U].
  rewrite open_nbhsE => -[oU Ux] UA.
  exists U; split => //; last by move/nbhs_singleton : Ux.
  split => //.
  apply: sub_finite_set finFA.
  move=> X; rewrite /restr_sets/= => -[FX XU0]; split=> //.
  apply: subset_nonempty XU0.
  exact: setIS.
apply/(closed_open_coverT_subspace _ cover_UU).
move=> U [oU finFU].
rewrite closed_subspaceTI.
rewrite setI_bigcupr.
rewrite restr_sets_bigcupIl.
apply: closed_bigcup.
  exact: finFU.
move=> /= A FUA.
apply: closedI.
  exact: closed_subspaceT.
apply: closed_subspaceW.
apply: clF.
by case: FUA.
Qed.

End closed_locally_finite_bigcup_closed.

(* https://proofwiki.org/wiki/Closure_of_Union_contains_Union_of_Closures *)
Lemma subset_closure_bigcup (A : set (set T)) :
  \bigcup_(X in A) closure X `<=` closure (\bigcup_(X in A) X).
Proof.
apply: bigcup_sub => X AX.
by apply: closureS => ?; exists X.
Qed.

Lemma locally_finite_closure_bigcupE (A : set (set T)) :
locally_finite A ->
  closure (\bigcup_(X in A) X) = \bigcup_(X in A) (closure X).
Proof.
move=> lA.
have lcA : locally_finite (closure @` A).
  exact: closures_locally_finite.
have cUcA : closed (\bigcup_(B in A) (closure B)).
  rewrite -(bigcup_image _ closure)/=.
  apply: closed_locally_finite_bigcup_closed.
  - exact: closures_locally_finite.
  - move=> _ [? _ <-]; exact: closed_closure.
rewrite eqEsubset; split.
- rewrite ((closure_id _).1 cUcA); apply: closureS.
  by apply: subset_bigcup => ? _; exact: subset_closure.
- exact: subset_closure_bigcup.
Qed.

End locally_finite.

Definition is_subset2 {T : eqType} (A : set T) :=
  exists r s : T, r != s /\ A = [set r; s].

Module closure_bigcup.
Section closure_bigcup.
Context {R : realType}.

Lemma closure_open (I : set R) : open I -> is_interval I ->
  exists2 A : set R, (is_subset1 A \/ is_subset2 A) & closure I = I `|` A.
Proof.
move=> oI iI.
Admitted. (* but unused *)

Definition close_open (I : set R) (oI : open I) (iI : is_interval I) :=
  sval (cid2 (closure_open oI iI)).

Lemma closure_openE (I : set R) (oI : open I) (iI : is_interval I) :
  closure I = I `|` close_open oI iI.
Proof.
rewrite /close_open.
by case: cid2.
Qed.

Lemma closure_bigcup (I : nat -> set R) :
  trivIset [set: nat] I ->
  (forall q : nat, open (I q) /\ is_interval (I q)) ->
  closure (\bigcup_n I n) = \bigcup_n (closure (I n)).
Proof.
move=> tI /all_and2 [oI iI].
apply/seteqP; split; last first.
  move=> /= r [i _] Iir.
  rewrite (bigcup_setD1 i)//.
  rewrite closureU.
  by left.
have -> : \bigcup_n closure (I n) =
    \bigcup_n (I n `|` close_open (oI n) (iI n)).
  apply/seteqP; split => /= r.
    move=> [i _ Iir].
    exists i => //.
    move: Iir.
    rewrite (closure_openE (oI i) (iI i)) => -[].
      by left.
    by right.
  move=> [i _] [Iir|].
    exists i => //.
    rewrite closure_openE//.
    by left.
  move=> ir.
  exists i => //=.
  rewrite closure_openE.
  by right.
move=> x.
  rewrite closure_isolated_limit_point => -[[/set_mem[n _ Inx]] _|].
  exists n => //.
  by left.
move/limit_pointP => [x_ ].
admit.
Abort.

(* StackExchange :
  https://math.stackexchange.com/questions/195311/
  union-of-closure-of-sets-is-the-closure-of-the-union-true-for-finite-false-for
 *)
Lemma in_mem_closedP (x : R) (A : set R) :
  closure A x <->
 (forall U, nbhs x U -> U `&` A !=set0).
Proof.
Admitted.

Lemma closure_bigcup0 (A : (set R)^nat) n :
  closure (\bigcup_(i < n) (A i)) = \bigcup_(i < n) (closure (A i)).
Proof.
rewrite eqEsubset; split; last first.
  apply: bigcup_sub => i /= iltn.
  by apply: closureS; exact: bigcup_sup.
apply: subsetC2.
move=> x.
rewrite -setTD/= => -[_ H].
have : forall i : 'I_ n, exists U' : set R, nbhs x U' /\ U' `&` A i = set0.
  move=> i.
  move: H => /exists2P/forallNP/(_ i).
  move/not_andP => [//=|].
  move/in_mem_closedP.
  move/existsNP => [U'].
  move/not_implyP => [xU'].
  move/set0P/negP/negbNE/eqP => UAi0.
  by exists U'.
move/choice => [U0 /all_and2[xU disjU]].
move/in_mem_closedP.
apply/existsNP.
Abort.

End closure_bigcup.
End closure_bigcup.

Section bigcup_cintsub.
Context {R : realType}.

Definition nondeg_interval :=
[set A : set R | is_interval A /\ ~ is_subset1 A].

Lemma nondeg_intervalP A : nondeg_interval A <->
  [/\ is_interval A, A !=set0 & inf A < sup A].
Proof.
split.
- move=> [itvA Nsub1A].
  split => //.
  + apply/set0P/negP; move/eqP => A0; apply: Nsub1A.
    by rewrite A0.
  + apply: has_bound_not_subset1_inf_sup.
    * 
      admit.
    * admit.
  + admit.
- move=> [itvA A0 inf_sup].
  split => //.
  admit.
Abort.

Definition nondeg_set :=
[set A : set R | closure (interior A) = A].

Definition cintsub (A C : set R) :=
  [/\ closed A, is_interval A & A `<=` C].

(*
bigcup_ointsub =
fun R : realType =>
let ointsub :=
  fun A U : set R => [/\ open A, is_interval A & A `<=` U] in
let ointsub_rat :=
  fun (U : set R) (q : rat) => [set A | ointsub A U /\ A (ratr q)]
  in
fun (U : set R) (q : rat) => \bigcup_(A in ointsub_rat U q) A
     : forall [R : realType], set R -> rat -> set R
*)

Lemma closed_disjoint (A : set R) : compact A -> nondeg_set A ->
   exists I : (set R)^nat,
[/\ (forall n, closed (I n)), (forall n, is_interval (I n)),
  trivIset [set: nat] I & A = \bigcup_n I n].
Proof.
Abort.


End bigcup_cintsub.

Section closed_disjoint.
Context {R : realType}.

Lemma unprovable_closed_disjoint (C : set R) : (closed C) ->
 exists I : (set R)^nat,
[/\ (forall n, closed (I n)), (forall n, is_interval (I n)),
  trivIset [set: nat] I & C = \bigcup_n I n].
Proof.
(* counter exaample: Cantor set
 * Cantor set is compact but uncountable union of closed set(singleton)
 *) Abort.

Lemma closed_disjoint (C : set R) : compact C ->
 exists I : (set R)^nat,
[/\ (forall n, closed (I n)), (forall n, is_interval (I n)),
  trivIset [set: nat] I & C = \bigcup_n I n].
Proof.
move=> cC.
(* if C is compact, there is a closed interval I0 such that
   C `<=` I0. *)
set I0 := Rhull C.
have I0E : I0 = `[inf C, sup C].
  rewrite /I0/Rhull.
  rewrite ifT//=; last first.
    apply: asboolT.
    exists (inf C).
    move=> x Cx.
    admit.
  admit.
(* Since ~` C is open, ~` C is written by countable union of open intervals
   by disjoint_open *)
have oCC : open (~` C).
  rewrite openC.
  exact: compact_closed.
have [U ] := OpenSetDisjointItvs.open_disjoint_itv oCC.
move=> [/all_and2[oU iU]] disjU cCU.
(* I0 `\` ~` C is countable union of closed interval? *)
Abort.

End closed_disjoint.

Section lebesgue_measure_closure.
Context {R : realType}.
Notation mu := lebesgue_measure.

Lemma bigcup_closure (B: nat -> set R) :
(forall i, is_interval (B i)) -> (forall i, ~ is_subset1 (B i)) ->
  trivIset [set: nat] B ->
closure (\bigcup_i B i) = \bigcup_i (closure (B i)).
Proof.
move=> disjB.
rewrite eqEsubset; split.
- move=> x.
  rewrite closure_isolated_limit_point/= => -[|].
  + rewrite /isolated => -[/set_mem[n In Bnx] ?].
    exists n => //.
    exact: subset_closure.
  + move/limit_pointP.
    move=> [/= p_ [pB px cvgp]].
 (* rewrite /limit_point/= => limpx. *)
 (*    pose e (n : nat) : R := n%:R^-1. *)
 (*    pose U n := (ball x (e n)). *)
 (*    poset n_ (i : nat) := proj1_sig ( *)
Abort.

Lemma lebesgue_measure_closure_open (A : set R) : open A ->
  mu A = mu (closure A).
Proof.
move=> oA.
have [->|] := eqVneq A set0.
  by rewrite closure0.
move/set0P => neA.
pose s := @open_disjoint_itv _ _ oA.
rewrite [in LHS](open_disjoint_itv_bigcup oA).
have ccA : closed (closure A).
  exact: closed_closure.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite le_measure ?inE//.
  - apply: bigcup_measurable => // k _.
    apply: open_measurable.
    exact: open_disjoint_itv_open.
  - exact: closed_measurable.
  rewrite -(open_disjoint_itv_bigcup oA).
  exact: subset_closure.
(*  move=> [:tmp].
  rewrite le_measure ?inE//.
    abstract: tmp.
    apply: bigcup_measurable => // k _.
    apply: open_measurable.
    by have [] := oiI k.
  apply: closed_measurable.
  exact: closed_closure.
  rewrite AE.
  exact: subset_closure.
*)
rewrite measure_bigcup//=; last 2 first.
  move=> n _.
  apply: is_interval_measurable.
  exact: open_disjoint_itv_is_interval.
  exact: open_disjoint_itv_trivIset.
Abort.

End lebesgue_measure_closure.

(* NB: work starts here *)

Lemma measure_is_completeP {d} {T : measurableType d} {R : realType}
  (mu : {measure set T -> \bar R}) :
  measure_is_complete mu <->
  (forall B, measurable B -> mu B = 0 -> forall A, A `<=` B -> measurable A).
Proof.
split.
- by move=> cmu B mB B0 A AB; apply: cmu; exists B.
- by move=> Hmu A [B [mB B0 AB]]; exact: Hmu AB.
Qed.

(*mu^*(A)=0 -> A satisfies caratheodory criterion

https://math.stackexchange.com/questions/2913728/complete-measures-and-complete-sigma-algebras*)

(*
Lemma Gdelta_restriction_open (R : topologicalType) (S U : set R) :
Gdelta S -> open U -> S `<=` U -> exists (s_ : (set R)^nat),
  [/\ (forall n, s_ n `<=` U), (forall n, open (s_ n)) & S = \bigcap_i s_ i].
Proof.
move=> [s'_ os'_ US] oU SU.
exists (fun n => (s'_ n) `&` U); split.
    by move=> ?; apply: subIsetr.
  by move=> ?; apply: openI.
by rewrite bigcapIl// setIidl// -US.
Qed.

Definition Gdelta_restr (R :topologicalType) (S U : set R)
(GdeltaS : Gdelta S) (openU : open U) (SU : S `<=` U) :=
sval (cid (Gdelta_restriction_open GdeltaS openU SU)).

Arguments Gdelta_restr {R} S U.

Lemma Gdelta_restrE (R : topologicalType) (S U : set R)
(GdeltaS : Gdelta S) (openU : open U) (SU : S `<=` U) (n : nat) :
  let S_ := sval (cid2 GdeltaS) in
  Gdelta_restr S U GdeltaS openU SU n = U `&` (S_ n) .
Proof.
move=> S_.
rewrite /S_.
have := Gdelta_restriction_open GdeltaS openU SU.
rewrite /Gdelta_restr.
case: cid.
Abort.

Lemma Gdelta_restriction_Gdelta (R : topologicalType) (S U : set R) :
Gdelta S -> Gdelta U -> S `<=` U -> exists (s_ : (set R)^nat),
  [/\ (forall n, s_ n `<=` U), (forall n, open (s_ n)) & S = \bigcap_i s_ i].
Proof.
move=> GdS [u'_ ou'_ UU] SU.
have Su'_ n : S `<=` u'_ n.
  admit.
have Gdr n := Gdelta_restr S (u'_ n) GdS (ou'_ n) (Su'_ n).
exists (fun n => Gdr n n).
split.
- move=> n.
  move=> x.
Abort.

(*Lemma Gdelta_restrS (R : topologicalType) (U S : set R)
(GdS : Gdelta S) (oU : open U) (SU : S `<=` U) :
  forall n, Gdelta_restr GdS oU SU n `<=` U.
Proof.
move=> n.
rewrite /Gdelta_restr.
have := Gdelta_restriction_open GdS oU SU.
case: cid.
rewrite /=.
move=> x.
by move=> [].
*)
 *)

Section for_abs_cont.
Context {R : realType}.

Lemma incl_itv_lb a (b : itv_bound R) n (B : 'I_n -> R * R) :
  (forall i, (B i).1 < (B i).2) ->
  (forall i, `](B i).1, (B i).2[ `<=`
             [set` Interval (BLeft a) b] (*NB: closed on the left*)) ->
  forall i, a <= (B i).1.
Proof.
move=> B12 Bab i; rewrite leNgt; apply/negP => Bi1a.
have := Bab i.
move=> /(_ (((B i).1 + minr a (B i).2)/2)).
rewrite /= !in_itv/= midf_lt//=; last by rewrite lt_min Bi1a B12.
have : ((B i).1 + minr a (B i).2) / 2 < (B i).2.
  by rewrite ltr_pdivrMr// mulr_natr mulr2n ltr_leD// ge_min lexx orbT.
move=> /[swap] /[apply] /andP[+ _].
rewrite ler_pdivlMr// mulr_natr mulr2n leNgt => /negP; apply.
by rewrite ltr_leD// ge_min lexx.
Qed.

Lemma incl_itv_lb_nat a (b : itv_bound R) n (B : nat -> R * R) :
  (forall i, (i < n)%N -> (B i).1 < (B i).2) ->
  (forall i, (i < n)%N -> `](B i).1, (B i).2[ `<=`
             [set` Interval (BLeft a) b] (*NB: closed on the left*)) ->
  forall i, (i < n)%N -> a <= (B i).1.
Proof.
move: n => [_ _ []//|n] H1 H2 i ni.
have /= := (@incl_itv_lb a b n.+1 (B \o @inord n) _ _ (Ordinal ni)).
rewrite inordK//; apply => j.
- exact: H1.
- exact: H2.
Qed.

Lemma incl_itv_ub (a : itv_bound R) b n (B : 'I_n -> R * R) :
  (forall i, (B i).1 < (B i).2) ->
  (forall i, `](B i).1, (B i).2[ `<=`
              [set` Interval a (BRight b)] (*NB: closed on the right*)) ->
  forall i, (B i).2 <= b.
Proof.
move=> B12 Bab i; rewrite leNgt; apply/negP => Bi2b.
have := Bab i.
move=> /(_ ((maxr (B i).1 b + (B i).2)/2)).
rewrite /= !in_itv/= midf_lt//=; last by rewrite gt_max Bi2b B12.
rewrite andbT.
have : (B i).1 < (maxr (B i).1 b + (B i).2) / 2.
  by rewrite ltr_pdivlMr// mulr_natr mulr2n ler_ltD// le_max lexx.
move=> /[swap] /[apply] /andP[_].
rewrite ler_pdivrMr// mulr_natr mulr2n leNgt => /negP; apply.
by rewrite ler_ltD// le_max lexx orbT.
Qed.

Lemma incl_itv_ub_nat (a : itv_bound R) b n (B : nat -> R * R) :
  (forall i, (i < n)%N -> (B i).1 < (B i).2) ->
  (forall i, (i < n)%N -> `](B i).1, (B i).2[ `<=`
              [set` Interval a (BRight b)] (*NB: closed on the right*)) ->
  forall i, (i < n)%N -> (B i).2 <= b.
Proof.
move: n => [_ _ []//|n] H1 H2 i ni.
have /= := (@incl_itv_ub a b n.+1 (B \o @inord n) _ _ (Ordinal ni)).
rewrite inordK//; apply => j.
- exact: H1.
- exact: H2.
Qed.

End for_abs_cont.

Lemma disjoint_itv_le {R : realType } (a b c d : R) : (a < b)%R -> (c < d)%R ->
  `]a, b[%classic `&` `]c, d[%classic = set0 -> (b <= c \/ d <= a)%R.
Proof.
move=> ab cd abcd.
have [bc|cb] := leP b c; [by left|right].
rewrite leNgt; apply/negP => ad.
move: abcd; rewrite -subset0.
move/(_ ((maxr a c + minr b d) / 2)); apply; split =>/=.
  rewrite in_itv /maxr /minr/=.
  case: ifPn => ac.
    case: ifPn => bd.
      rewrite (lt_le_trans ac)//= ?(midf_le (ltW _))//.
      by rewrite midf_lt//.
    rewrite (lt_le_trans ac)//= ?(midf_le (ltW _))//.
    rewrite -leNgt in bd.
    rewrite (lt_le_trans _ bd)//.
    by rewrite midf_lt//.
  rewrite -leNgt in ac.
  case: ifPn => bd.
    by rewrite !midf_lt.
  rewrite -leNgt in bd.
  rewrite midf_lt//=.
  rewrite (lt_le_trans _ bd)//.
  by rewrite midf_lt//.
rewrite in_itv /maxr /minr/=.
case: ifPn => ac.
  case: ifPn => bd.
    by rewrite midf_lt//= (le_lt_trans _ bd)// midf_le//= ltW.
  by rewrite midf_lt//= midf_lt//.
rewrite -leNgt in ac.
case: ifPn => [bd|].
  rewrite (le_lt_trans ac)//= ?midf_lt//.
  by rewrite (le_lt_trans _ bd)// midf_le// ltW.
rewrite -leNgt => bd.
by rewrite (le_lt_trans ac) midf_lt.
Qed.

Section absolute_continuity_def.
Context {R : realType}.

Definition abs_cont (a b : R) (f : R -> R) := forall e : {posnum R},
  exists d : {posnum R}, forall n (B : nat -> R * R),
    [/\ (forall i, (i < n)%N ->
          (B i).1 < (B i).2 /\ `](B i).1, (B i).2[ `<=` `[a, b]),
        trivIset `I_n (fun i => `](B i).1, (B i).2[%classic) &
        \sum_(k < n) ((B k).2 - (B k).1) < d%:num] ->
        \sum_(k < n) (f (B k).2 - f ((B k).1)) < e%:num.

Definition abs_cont_order (a b : R) (f : R -> R) := forall e : {posnum R},
  exists d : {posnum R}, forall n (B : nat -> R * R),
    [/\ (forall i, (i < n)%N ->
          ((B i).1 < (B i).2 /\ `](B i).1, (B i).2[ `<=` `[a, b])),
        (forall i j : 'I_n, (i < j)%N -> (B i).2 <= (B j).1),
        trivIset `I_n (fun i => `](B i).1, (B i).2[%classic) &
        \sum_(k < n) ((B k).2 - (B k).1) < d%:num] ->
        \sum_(k < n) (f (B k).2 - f ((B k).1)) < e%:num.

End absolute_continuity_def.

Section abs_contP.
Context {R : realType}.

From mathcomp Require Import perm fingroup.

Let lt_itv (B : (R * R)^nat) i j := (i == j) || ((B i).2 <= (B j).1).

Lemma abs_contP (a b : R) (f : R -> R) : abs_cont a b f <-> abs_cont_order a b f.
Proof.
split=> [h e|h e].
  have {h}[d h] := h e.
  by exists d => n B [BS B21 tB] Bd; exact: (h n B).
have {h}[d h] := h e; exists d => n B [BS tB Bd].
pose ordered_indices : seq nat := sort (lt_itv B) (iota 0 n).
pose g_nat : nat -> nat := nth 0 ordered_indices.
have g_nat_ub (i : 'I_n) : (g_nat i < n)%N.
  apply/(@all_nthP _ [pred x | x < n]%N).
    by apply/allP => x /=; rewrite mem_sort mem_iota add0n leq0n.
  by rewrite size_sort size_iota.
pose g : {ffun 'I_n -> 'I_n} := [ffun i => Ordinal (g_nat_ub i)].
have g_nat_inj : {in gtn n &, injective g_nat}.
  move=> /= i j /[!inE] ni nj.
  rewrite /g_nat /= /ordered_indices.
  have : uniq ordered_indices by rewrite sort_uniq// iota_uniq.
  move/uniqP => /(_ 0) /[apply].
  rewrite !inE !size_sort !size_iota.
  exact.
have g_inj : injectiveb g.
  apply/injectiveP => /= i j.
  rewrite /g /= !ffunE.
  move/(congr1 val)/g_nat_inj.
  rewrite !inE => /(_ (ltn_ord i) (ltn_ord j)) ij.
  exact/val_inj.
pose Bg : 'I_ n -> R * R := B \o (fun x => g x).
pose Bg_nat (i : nat) : R * R := match Bool.bool_dec (i < n)%N true with
  | left H => Bg (@Ordinal n _ H)
  | _ => B 0
  end.
have nbBg_nat (i j : 'I_n ) : (i < j)%N -> (Bg_nat i).2 <= (Bg_nat j).1.
  move=> ij.
  rewrite /Bg_nat; case: Bool.bool_dec => [ni|]; last by rewrite ltn_ord.
  case: Bool.bool_dec => [nj|]; last by rewrite ltn_ord.
  rewrite /Bg /=.
  suff: lt_itv B (g_nat i) (g_nat j).
    rewrite /lt_itv => /predU1P[|].
      move/injectiveP in g_inj.
      move/g_nat_inj.
      rewrite !inE ni nj => /(_ erefl erefl) ji.
      by rewrite ji ltnn in ij.
    by rewrite /g/= !ffunE/=; exact.
  have := @sorted_ltn_nth_in _ _ (lt_itv B).
  apply => //.
  - move=> x y z.
    rewrite !mem_sort !mem_iota !add0n !leq0n/= => xn yn zn.
    rewrite /lt_itv => /predU1P[->|yx].
      move=> /predU1P[->|->].
        by rewrite eqxx.
      by rewrite orbT.
    move=> /predU1P[<-|xz].
      by rewrite yx orbT.
    have [->//|yz/=] := eqVneq y z.
    rewrite (le_trans yx)// (le_trans _ xz)// ltW//.
    exact: (BS _ xn).1.
  - apply: (@sort_sorted_in _ [pred x | x < n]%N).
      move=> x y; rewrite !inE => xn yn.
      rewrite /lt_itv; have [//|/= xy] := eqVneq x y.
      apply/orP/disjoint_itv_le.
      - exact: (BS _ xn).1.
      - exact: (BS _ yn).1.
      - by move/trivIsetP : tB => /(_ (Ordinal xn) (Ordinal yn)); exact.
    by apply/allP => /= y; rewrite mem_iota leq0n.
  - by rewrite inE size_sort size_iota.
  - by rewrite inE size_sort size_iota.
pose permg : {perm 'I_n} := Perm g_inj.
have K : \sum_(k < n) (f (B k).2 - f (B k).1) =
     \sum_(k < n) (f (Bg_nat k).2 - f (Bg_nat k).1).
  rewrite (reindex_onto permg permg^-1%g)//=; last by move=> i _; rewrite permKV.
  apply/eq_big.
    by move=> i; rewrite /= permK eqxx.
  move=> i _.
  rewrite /Bg_nat; case: Bool.bool_dec => /=; last by rewrite (ltn_ord i).
  move=> ni.
  rewrite /Bg/= /permg/=.
  suff : Perm g_inj i = g (Ordinal ni) by move=> <-.
  rewrite unlock/=.
  rewrite (_ : Ordinal ni = i)//.
  exact/val_inj.
rewrite K; apply: h; split => //.
- move=> i ni; split.
    rewrite /Bg_nat; case: Bool.bool_dec => //= ni'.
    rewrite /Bg/=.
    exact: (BS _ _).1.
  rewrite /Bg_nat; case: Bool.bool_dec => //= ni'.
  rewrite /Bg/=.
  exact: (BS _ _).2.
- apply/trivIsetP => /= i j ni nj ij.
  rewrite /Bg_nat; case: Bool.bool_dec => //= ni'.
  rewrite /Bg/=; case: Bool.bool_dec => //= nj'.
  move/trivIsetP : tB; apply => //=.
  apply: contra ij => /eqP.
  rewrite {permg}.
  move: g_inj => /injectiveP g_inj H.
  have /(_ _)/(congr1 val)/eqP := g_inj (Ordinal ni') (Ordinal nj').
  apply.
  exact/val_inj.
- rewrite [ltLHS](_ : _ = \sum_(k < n) ((B k).2 - (B k).1))//.
  rewrite [RHS](reindex_onto permg permg^-1%g)//=; last by move=> i _; rewrite permKV.
  apply/eq_big.
    by move=> i; rewrite /= permK eqxx.
  move=> i _.
  rewrite /Bg_nat; case: Bool.bool_dec => [ni|]; last by rewrite (ltn_ord _).
  rewrite /Bg/= /permg/=.
  suff : Perm g_inj i = g (Ordinal ni) by move=> <-.
  rewrite unlock/=.
  rewrite (_ : Ordinal ni = i)//.
  exact/val_inj.
Qed.

End abs_contP.

Section tmp.
Context {R : realType}.

Lemma nonincreasing_at_right_cvgr2 (f : R -> R) a (b : itv_bound R) :
 (BRight a < b)%O ->
    {in Interval (BLeft a) b &, nonincreasing_fun f} ->
    has_ubound (f @` [set` Interval (BLeft a) b]) ->
  f x @[x --> a ^'+] --> sup (f @` [set` Interval (BLeft a) b]).
Proof.
move=> ab lef ubf; set M := sup _.
have supf : has_sup [set f x | x in [set` Interval (BLeft a) b]].
  split => //; case: b ab {lef ubf M} => [[|] t ta|[]] //=.
  - exists (f ((a + t) / 2)), ((a + t) / 2) => //=.
    rewrite in_itv/= midf_le/=; last by rewrite ltW.
    by rewrite midf_lt//.
  - exists (f ((a + t) / 2)), ((a + t) / 2) => //=.
    rewrite in_itv/=.
    rewrite midf_le//=; last exact: ltW.
    by rewrite midf_le// ltW.
  - exists (f (a + 1)), (a + 1) => //=.
    by rewrite in_itv/= andbT lerDl.
apply/(@cvgrPdist_le _ R^o) => _/posnumP[e].
have {supf} [p [ap pb]] :
    exists p, [/\ a <= p, (BLeft p < b)%O & M - e%:num <= f p].
  have [_ -[p apb] <- /ltW efp] := sup_adherent (gt0 e) supf.
  move: apb; rewrite /= in_itv/= -[X in _ && X]/(BLeft p < b)%O => /andP[ap pb].
  by exists p; split => //.
move: ap; rewrite le_eqVlt => /predU1P[?|ap].
  subst p.
  admit.
rewrite lerBlDr {}/M.
move: b ab pb lef ubf => [[|] b|[//|]] ab pb lef ubf; set M := sup _ => Mefp.
- near=> r; rewrite ler_distl; apply/andP; split.
  + suff: f r <= M by apply: le_trans; rewrite lerBlDr lerDl.
    apply: ub_le_sup => //=; exists r => //; rewrite in_itv/=.
    apply/andP; split; near: r; [|exact: nbhs_right_lt].
    exact: nbhs_right_ge.
  + rewrite (le_trans Mefp)// lerD2r lef//=; last 2 first.
      by rewrite in_itv/= ltW//.
      near: r.
      by apply: nbhs_right_le.
    by apply/andP; split; near: r; [exact: nbhs_right_ge|exact: nbhs_right_lt].
- near=> r; rewrite ler_distl; apply/andP; split.
  + suff: f r <= M by apply: le_trans; rewrite lerBlDr lerDl.
    apply: ub_le_sup => //=; exists r => //; rewrite in_itv/=.
    apply/andP; split; near: r; [exact: nbhs_right_ge|].
    by apply: nbhs_right_le.
  + rewrite (le_trans Mefp)// lerD2r lef//=; last 2 first.
      by rewrite in_itv/= ltW.
      near: r.
      by apply: nbhs_right_le.
    by apply/andP; split; near: r; [exact: nbhs_right_ge|exact: nbhs_right_le].
- near=> r; rewrite ler_distl; apply/andP; split.
  suff: f r <= M by apply: le_trans; rewrite lerBlDr lerDl.
  apply: ub_le_sup => //=; exists r => //; rewrite in_itv/= andbT.
    by near: r; apply: nbhs_right_ge.
  rewrite (le_trans Mefp)// lerD2r lef//.
  - by rewrite in_itv/= andbT; near: r; exact: nbhs_right_ge.
  - by rewrite in_itv/= ltW.
  - near: r.
    by apply: nbhs_right_le.
Unshelve. all: by end_near. Abort.

Lemma nondecreasing_at_right_cvgr2 (f : R -> R) a (b : itv_bound R) : (BLeft a < b)%O ->
    {in Interval (BLeft a) b &, nondecreasing_fun f} ->
    has_lbound (f @` [set` Interval (BLeft a) b]) ->
  f x @[x --> a ^'+] --> inf (f @` [set` Interval (BLeft a) b]).
Proof.
move=> ab nif hlb; set M := inf _.
have ndNf : {in Interval (BLeft a) b &, nonincreasing_fun (\- f)}.
  by move=> r s rab sab /nif; rewrite lerN2; exact.
have hub : has_ubound [set (\- f) x | x in [set` Interval (BLeft a) b]].
  apply/has_ub_lbN; rewrite image_comp/=.
  rewrite [X in has_lbound X](_ : _ = f @` [set` Interval (BLeft a) b])//.
  by apply: eq_imagel => y _ /=; rewrite opprK.
(*have /cvgN := nonincreasing_at_right_cvgr ab ndNf hub.
rewrite opprK [X in _ --> X -> _](_ : _ =
    inf (f @` [set` Interval (BRight a) b]))//.
by rewrite /inf; congr (- sup _); rewrite image_comp/=; exact: eq_imagel.
Qed.*) Abort.

Local Open Scope ereal_scope.

Lemma nondecreasing_at_right_cvge2 (f : R -> \bar R) a (b : itv_bound R) :
    (BLeft a < b)%O ->
    {in Interval (BLeft a) b &, nondecreasing_fun f} ->
  f x @[x --> a ^'+] --> ereal_inf (f @` [set` Interval (BLeft a) b]).
Proof.
move=> ab ndf; set S := (X in ereal_inf X); set l := ereal_inf S.
have [Snoo|Snoo] := pselect (S -oo).
(*  case: (Snoo) => N/=.
  rewrite in_itv/= -[X in _ && X]/(BLeft N < b)%O => /andP[aN Nb] fNpoo.
  have Nf n : (a < n <= N)%R -> f n = -oo.
    move=> /andP[an nN]; apply/eqP.
    rewrite eq_le leNye andbT -fNpoo ndf//.
      by rewrite in_itv/= -[X in _ && X]/(BLeft n < b)%O an (le_lt_trans _ Nb).
    by rewrite in_itv/= -[X in _ && X]/(BLeft N < b)%O (lt_le_trans an nN).
  have -> : l = -oo.
    by rewrite /l /ereal_inf /ereal_sup supremum_pinfty//=; exists -oo.
  apply: cvg_near_cst; exists (N - a)%R => /=; first by rewrite subr_gt0.
  move=> y /= + ay; rewrite ltr0_norm ?subr_lt0// opprB => ayNa.
  by rewrite Nf// ay/= -(subrK a y) -lerBrDr ltW.*) admit.
have [lnoo|lnoo] := eqVneq l -oo.
(*
  rewrite lnoo; apply/cvgeNyPle => M.
  have /ereal_inf_lt[x [y]]/= : M%:E > l by rewrite lnoo ltNyr.
  rewrite in_itv/= -[X in _ && X]/(BLeft y < b)%O/= => /andP[ay yb] <- fyM.
  exists (y - a)%R => /=; first by rewrite subr_gt0.
  move=> z /= + az.
  rewrite ltr0_norm ?subr_lt0// opprB ltrBlDr subrK => zy.
  rewrite (le_trans _ (ltW fyM))// ndf ?ltW//.
    by rewrite in_itv/= -[X in _ && X]/(BLeft z < b)%O/= az/= (lt_trans _ yb).
  by rewrite in_itv/= -[X in _ && X]/(BLeft y < b)%O/= (lt_trans az zy). *)admit.
have [fpoo|fpoo] := pselect {in Interval (BRight a) b, forall x, f x = +oo}.
(*
  rewrite {}/l in lnoo *; rewrite {}/S in Snoo lnoo *.
  rewrite [X in ereal_inf X](_ : _ = [set +oo]).
    rewrite ereal_inf1; apply/cvgeyPgey; near=> M.
    move: b ab {ndf lnoo Snoo} fpoo => [[|] b|[//|]] ab fpoo.
    - near=> x; rewrite fpoo ?leey// in_itv/=.
      by apply/andP; split; near: x; [exact: nbhs_right_gt|exact: nbhs_right_lt].
    - near=> x; rewrite fpoo ?leey// in_itv/=.
      by apply/andP; split; near: x; [exact: nbhs_right_gt|exact: nbhs_right_le].
    - near=> x; rewrite fpoo ?leey// in_itv/= andbT.
      by near: x; exact: nbhs_right_gt.
  apply/seteqP; split => [_ [n _] <- /[!fpoo]//|_ ->].
  move: b ab ndf lnoo Snoo fpoo => [[|] s|[//|]] ab ndf lnoo Snoo fpoo /=.
  - by exists ((a + s) / 2)%R; rewrite ?fpoo// in_itv/= !midf_lt.
  - by exists ((a + s) / 2)%R; rewrite ?fpoo// in_itv/= !(midf_lt, midf_le)// ltW.
  - by exists (a + 1)%R; rewrite ?fpoo// in_itv/= andbT ltrDl.*) admit.
have [/ereal_inf_pinfty lpoo|lpoo] := eqVneq l +oo.
  (*by exfalso; apply/fpoo => r rab; rewrite (lpoo (f r))//; exists r.*) admit.
have l_fin_num : l \is a fin_num by admit (*rewrite fin_numE lpoo lnoo*).
set A := [set r | [/\ (a < r)%R, (BLeft r < b)%O & f r != +oo]].
have f_fin_num r : r \in A -> f r \is a fin_num.
  rewrite inE /A/= => -[ar rb] frnoo; rewrite fin_numE frnoo andbT.
  apply: contra_notN Snoo => /eqP frpoo.
  (*by exists r => //=; rewrite in_itv/= -[X in _ && X]/(BLeft r < b)%O ar rb.*) admit.
have [x [ax xb fxpoo]] : A !=set0.
  apply/set0P/negP => /eqP A0; apply/fpoo => x.
  rewrite in_itv/= -[X in _ && X]/(BLeft x < b)%O => /andP[ax xb].
  apply/eqP/negPn/negP => unnoo.
  by move/seteqP : A0 => [+ _] => /(_ x); apply; rewrite /A/= ax.
have axA r : (a < r <= x)%R -> r \in A.
  move=> /andP[ar rx]; move: (rx) => /ndf rafx; rewrite /A /= inE; split => //.
    by rewrite (le_lt_trans _ xb).
  apply/negP => /eqP urnoo.
  move: rafx; rewrite urnoo.
  (*rewrite in_itv/= -[X in _ && X]/(BLeft r < b)%O ar/=.
  rewrite in_itv/= -[X in _ && X]/(BLeft x < b)%O ax/=.
  by rewrite leye_eq (negbTE fxpoo) -falseE; apply; rewrite (le_lt_trans _ xb).*) admit.
rewrite -(@fineK _ l)//; apply/fine_cvgP; split.
  exists (x - a)%R => /=; first by rewrite subr_gt0.
  move=> z /= + az.
  rewrite ltr0_norm ?subr_lt0// opprB ltrBlDr subrK// => zx.
  by rewrite f_fin_num// axA// az/= ltW.
set g := fun n => if (a < n < x)%R then fine (f n) else fine (f x).
have <- : inf [set g x | x in [set` Interval (BLeft a) b]] = fine l.
  apply: EFin_inj; rewrite -ereal_inf_EFin//; last 2 first.
    - exists (fine l) => /= _ [m _ <-]; rewrite /g /=.
      case: ifPn => [/andP[am mx]|].
        rewrite fine_le// ?f_fin_num//; first by rewrite axA// am (ltW mx).
        apply: ereal_inf_lbound; exists m => //=.
        (*rewrite in_itv/= -[X in _ && X]/(BLeft m < b)%O am/=.
        by rewrite (le_lt_trans _ xb) ?ltW.*) admit.
      rewrite negb_and -!leNgt => /orP[ma|xm].
        rewrite fine_le// ?f_fin_num ?inE//.
        apply: ereal_inf_lbound; exists x => //=.
(*        by rewrite in_itv/= -[X in _ && X]/(BLeft x < b)%O ax xb.*) admit.
      rewrite fine_le// ?f_fin_num ?inE//.
      apply: ereal_inf_lbound; exists x => //=.
(*      by rewrite in_itv/= -[X in _ && X]/(BLeft x < b)%O ax xb.*) admit.
    - rewrite {}/l in lnoo lpoo l_fin_num *.
      rewrite {}/S in Snoo lnoo lpoo l_fin_num *.
      rewrite {}/A in f_fin_num axA *.
      move: b ab {xb ndf lnoo lpoo l_fin_num f_fin_num Snoo fpoo axA} =>
            [[|] s|[//|]] ab /=.
      + exists (g ((a + s) / 2))%R, ((a + s) / 2)%R => //=.
        (*by rewrite /= in_itv/= !midf_lt.*) admit.
      + exists (g ((a + s) / 2))%R, ((a + s) / 2)%R => //=.
        by rewrite /= in_itv/= !(midf_lt, midf_le)// ltW.
      + exists (g (a + 1)%R), (a + 1)%R => //=.
(*        by rewrite in_itv/= andbT ltrDl.*) admit.
  rewrite fineK//; apply/eqP; rewrite eq_le; apply/andP; split; last first.
    apply: ereal_inf_le_tmp => _ /= [_ [m _] <-] <-.
    rewrite /g; case: ifPn => [/andP[am mx]|].
      rewrite fineK// ?f_fin_num//; last by rewrite axA// am ltW.
      exists m => //=.
(*      by rewrite in_itv/= -[X in _ && X]/(BLeft m < b)%O am/= (lt_trans _ xb).*)admit.
    rewrite negb_and -!leNgt => /orP[ma|xm].
      rewrite fineK//; last by rewrite f_fin_num ?inE.
      exists x => //=.
(*      by rewrite in_itv/= -[X in _ && X]/(BLeft x < b)%O ax xb.*) admit.
    exists x => /=.
(*      by rewrite in_itv/= -[X in _ && X]/(BLeft x < b)%O ax xb.*) admit.
    by rewrite fineK// f_fin_num ?inE.
  apply: le_ereal_inf_tmp=> /= y [m] /=.
  rewrite in_itv/= -[X in _ && X]/(BLeft m < b)%O => /andP[am mb] <-{y}.
  have [mx|xm] := ltP m x.
    apply: ereal_inf_lbound => /=; exists (fine (f m)); last first.
(*      by rewrite fineK// f_fin_num// axA// am (ltW mx).*) admit.
(*    by exists m; [rewrite in_itv/= am|rewrite /g am mx].*) admit.
  rewrite (@le_trans _ _ (f x))//; last first.
(*    by apply: ndf => //; rewrite in_itv//= ?ax ?am.*) admit.
  apply: ereal_inf_lbound => /=; exists (fine (f x)); last first.
    by rewrite fineK// f_fin_num ?inE.
(*  by exists x; [rewrite in_itv/= ax|rewrite /g ltxx andbF].*) admit.
suff: g x @[x --> a^'+] --> inf [set g x | x in [set` Interval (BLeft a) b]].
  apply: cvg_trans; apply: near_eq_cvg; near=> n.
  rewrite /g /=; case: ifPn => [//|].
  rewrite negb_and -!leNgt => /orP[na|xn].
    exfalso.
    move: na; rewrite leNgt => /negP; apply.
    by near: n; exact: nbhs_right_gt.
  suff nx : (n < x)%R by rewrite ltNge xn in nx.
  near: n; exists ((x - a) / 2)%R; first by rewrite /= divr_gt0// subr_gt0.
  move=> y /= /[swap] ay.
  rewrite ltr0_norm// ?subr_lt0// opprB ltrBlDr => /lt_le_trans; apply.
  by rewrite -lerBrDr ler_pdivrMr// ler_pMr// ?ler1n// subr_gt0.
(*apply: nondecreasing_at_right_cvgr2 => //.
- move=> m n; rewrite !in_itv/= -[X in _ && X]/(BLeft m < b)%O.
  rewrite -[X in _ -> _ && X -> _]/(BLeft n < b)%O.
  move=> /andP[am mb] /andP[an nb] mn.
  rewrite /g /=; case: ifPn => [/andP[_ mx]|].
    rewrite (lt_le_trans am mn) /=; have [nx|nn0] := ltP n x.
      rewrite fine_le ?f_fin_num ?ndf//; first by rewrite axA// am (ltW mx).
      by rewrite axA// (ltW nx) andbT (lt_le_trans am).
      by rewrite in_itv/= am.
      by rewrite in_itv/= an.
    rewrite fine_le ?f_fin_num//.
    + by rewrite axA// am (ltW (lt_le_trans mx _)).
    + by rewrite inE.
    + rewrite ndf//; last exact/ltW.
      by rewrite !in_itv/= am.
      by rewrite !in_itv/= ax.
  rewrite negb_and -!leNgt => /orP[|xm]; first by rewrite leNgt am.
  by rewrite (lt_le_trans am mn)/= ltNge (le_trans xm mn).
- exists (fine l) => /= _ [m _ <-]; rewrite /g /=.
  rewrite -lee_fin (fineK l_fin_num); apply: ereal_inf_lbound.
  case: ifPn => [/andP[am mn0]|].
    rewrite fineK//; last by rewrite f_fin_num// axA// am (ltW mn0).
    exists m => //=.
    by rewrite in_itv/= -[X in _ && X]/(BLeft m < b)%O am (lt_trans _ xb).
  rewrite negb_and -!leNgt => /orP[ma|xm].
    rewrite fineK//; first by exists x => //=; rewrite in_itv/= ax.
    by rewrite f_fin_num ?inE.
  by rewrite fineK// ?f_fin_num ?inE//; exists x => //=; rewrite in_itv/= ax.
Unshelve. all: by end_near. *) Abort.

End tmp.

Section absolute_continuity_lemmas.
Context {R : realType}.

Lemma abs_cont_der0 a b (f : R^o -> R^o) : a < b ->
  abs_cont a b f -> {ae @lebesgue_measure R, {in `[a, b], f^`() =1 cst 0}} ->
  {in `[a, b], forall c, f c = f a}.
Proof.
move=> ab abf Df0 c cab.
pose E := [set x | f^`() x = 0] `&` `[a, c].
suff: forall e : R, 0 < e -> `|f c - f a| <= e * (c - a + 1).
  move=> suf; move: cab; rewrite in_itv/= => /andP[ac _].
  apply/eqP; rewrite -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT.
  apply/ler_addgt0Pl => /= e e0; rewrite addr0.
  rewrite -(mulr1 e) -(@mulVf _ ((c - a + 1))); last first.
    by rewrite gt_eqF// ltr_pwDr// subr_ge0.
  by rewrite mulrA suf// divr_gt0// ltr_pwDr// subr_ge0.
move=> _/posnumP[e]; have [d de] := abf e.

Abort.

End absolute_continuity_lemmas.

(*
Section total_variation_lim.
Context {R : realType}.
Context (a b : R) (f : R -> R).
Context (ab : a < b).

(* subdivide itv_partition by mean *)
Let regular_itv_partition (n : nat) : seq R :=
 [seq (fun (j : nat) => (a + ((b - a) * j))) i | i <- iota 1 n].

Lemma total_variation_lim :
End.
*)

Section wip.
Context {R : realType}.

(* this would be used in abs_cont_bounded_variation *)
Lemma itv_partition_undup_merge (a b : R) (s t : seq R) :
  itv_partition a b s -> itv_partition a b t ->
  itv_partition a b (undup (merge <%R s t)).
Proof.
Abort.

Lemma abs_cont_bounded_variation (a b : R) (f : R -> R) :
  abs_cont a b f -> bounded_variation a b f.
Proof.
Abort.

End wip.

(* TODO: move to lebesgue_measure.v *)
Lemma lebesgue_measureT {R : realType} : (@lebesgue_measure R) setT = +oo%E.
Proof. by rewrite -set_itvNyy lebesgue_measure_itv. Qed.

Lemma completed_lebesgue_measureE {R : realType} :
  (@completed_lebesgue_measure R) = (@lebesgue_measure R).
Proof. by []. Qed.

Lemma completed_lebesgue_measure_itv {R : realType} (i : interval R) :
  completed_lebesgue_measure ([set` i] : set R) =
  (if i.1 < i.2 then (i.2 : \bar R) - i.1 else 0)%E.
Proof.
transitivity (lebesgue_measure [set` i]); last first.
  by rewrite lebesgue_measure_itv.
by rewrite completed_lebesgue_measureE.
Qed.

Lemma completed_lebesgue_measureT {R : realType} :
  (@completed_lebesgue_measure R) setT = +oo%E.
Proof.
by rewrite -set_itvNyy completed_lebesgue_measure_itv.
Qed.

Lemma wlength_idfun_le {R : realType} : forall A, R.-ocitv.-measurable A ->
  ((@wlength R idfun) A <= ((wlength idfun)^*)%mu A)%E.
Proof.
move=> A mA; apply: le_ereal_inf_tmp => /= _ [F [mF AF] <-].
by apply: (wlength_sigma_subadditive idfun mF mA AF).
Qed.

Section outer_measureT.
Context {R : realType}.

(*
  ref:https://heil.math.gatech.edu/6337/spring11/section1.1.pdf
  Lemma 1.17
*)

Local Notation mu := (((wlength idfun)^*)%mu).

Lemma lee_addltyPr (x : \bar R) : reflect (forall y, y%:E <= x)%E (x == +oo%E).
Proof.
apply/(iffP idP) => [/eqP -> y|]; first by rewrite leey.
move: x => [x lex|//|]; last by move/(_ 0); rewrite leeNy_eq.
rewrite eq_le leey/= leNgt; apply/negP => xoo.
have := lex (x + 1); rewrite leNgt => /negP; apply.
by rewrite lte_fin ltrDl.
Qed.

Lemma outer_measureT : (mu setT = +oo%E :> \bar R).
Proof.
apply/eqP/lee_addltyPr => y /=.
have [->|y0] := eqVneq y 0; first exact: outer_measure_ge0.
apply: (@le_trans _ _ (mu (`] (- `|y|)%R, `|y|%R ]%classic : set R)))%E.
  apply: (@le_trans _ _ (wlength idfun `](- normr y)%R, (normr y)])).
    rewrite wlength_itv/= lte_fin gtrN ?normr_gt0// opprK.
    by rewrite -EFinD lee_fin -[leLHS]addr0 lerD// ler_norm.
  by apply: wlength_idfun_le => //; exists (- normr y, normr y).
by apply: le_outer_measure.
Qed.

End outer_measureT.

Section lebesgue_regularity_outer_inf.
Local Close Scope ereal_scope.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).

(* Theorem 1.17, https://heil.math.gatech.edu/6337/spring11/section1.1.pdf *)
Lemma outer_regularity_outer0 (E : set R) (e : R) : (e > 0)%R ->
  exists U : set R, [/\ open U, E `<=` U & (mu E <= mu U <= mu E + e%:E)%E].
Proof.
move=> e0.
have [U [oU EU mUe]] := @outer_measure_open_le R E e e0.
exists U; split => //; apply/andP; split.
  by rewrite le_outer_measure.
exact: mUe.
Qed.

(* Theorem 1.17 https://heil.math.gatech.edu/6337/spring11/section1.1.pdf *)
(* was outer_regularity_outer *)
Lemma lebesgue_regularity_outer_inf (E : set R) :
  mu E = ereal_inf [set mu U | U in [set U | open U /\ E `<=` U]].
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: le_ereal_inf_tmp => /= r /= [A [oA EA] <-{r}].
  apply: ereal_inf_le_tmp => _ /= [] S_ AS_ <-; exists S_ => //.
  move: AS_ => [mS_ AS_].
  by split; [exact: mS_|exact: (subset_trans EA)].
- apply/lee_addgt0Pr => /= e e0.
  have [U [oU EU /andP[UE UEe]]] := outer_regularity_outer0 E e0.
  apply: ge_ereal_inf => /=.
  exists (mu U) => //.
  by exists U.
Qed.

Lemma outer_regularity_outer0_near (E A : set R) :
 open A ->
 E `<=` A ->
 (mu E < mu A)%E ->
 \forall e \near 0^'+,
  exists U : set R, [/\ open U, E `<=` U, U `<=` A & (mu E <= mu U <= mu E + e%:E)%E].
Proof.
move=> oA EA mEA.
near=> e.
have [->|] := eqVneq (mu E) +oo%E.
  exists A; split => //.
  rewrite leey andbT.
Abort.
(*
-set_itv_infty_infty lebesgue_measure_itv.
rewrite -ltey -ge0_fin_numE; last exact: outer_measure_ge0.
  admit.
rewrite -ltey -ge0_fin_numE; last exact: outer_measure_ge0.
move=> /[dup] mEfin => /lb_ereal_inf_adherent.
set infE := ereal_inf _.
have e20 : 0 < e / 2 by rewrite divr_gt0.
move=> /(_ _ e20)[x [/= Q EQ <- muEoo]].
have [/= T [QT TA TQ]] : exists T : nat -> set R,
    [/\ (forall k, Q k `<=` interior (T k)),
       (forall k, T k `<=` A) &
    (forall k, mu (T k) <= mu (Q k) + (e / (2 ^+ k.+2))%:E)%E].
  have mQfin k : mu (Q k) \is a fin_num.
    rewrite ge0_fin_numE//.
    apply: (@le_lt_trans _ _ (\sum_(0 <= k <oo) wlength idfun (Q k)))%E.
      rewrite /mu/= /lebesgue_stieltjes_measure/= /measure_extension/=.
      rewrite measurable_mu_extE /=; last by move: EQ => [+ _]; exact.
      by rewrite (nneseriesD1 k) // leeDl// nneseries_ge0.
    by rewrite (lt_le_trans muEoo)// leey.
  have /choice[T /= TH] : forall k, exists T : set R,
      [/\ open T, (Q k) `<=` T, T `<=` A & (mu (T `\` Q k) < (e / 2 ^+ k.+2)%:E)%E].
    move=> k.
    have /ocitvP[->|] : ocitv (Q k) by move: EQ => /cover_measurable/(_ k).
      by exists set0; split=> //; rewrite setD0 measure0 exprS lte_fin divr_gt0.
    move=> [[Qkl Qkr] lr] ->.
    exists `]Qkl, Qkr + (e / 2 ^+ k.+3) [%classic; split => //=.
    - exact: interval_open.
    - move=> y/=; rewrite !in_itv/= => /andP[-> yQkr].
      by rewrite (le_lt_trans yQkr)// ltrDl// divr_gt0.
    - rewrite (_ : _ `\` _ = `]Qkr, Qkr + e / 2 ^+ k.+3[%classic); last first.
        apply/seteqP; split => [y|y]/=.
          rewrite !in_itv/= => -[/andP[-> yQKr /negP]].
            by rewrite -ltNge => -> /=.
          rewrite !in_itv/= => /andP[H1 ->].
          rewrite andbT (lt_trans lr)//=; split => //.
          by apply/negP; rewrite -ltNge.
      rewrite lebesgue_measure_itv/= lte_fin ltrDl// divr_gt0//.
      rewrite -EFinD addrAC subrr add0r lte_fin.
      by rewrite ltr_pM2l// -!exprVn exprSr ltr_pdivrMr// ltr_pMr// ltr1n.
  exists T => k.
    have [oTk QkTk _] := TH k.
    by apply: (subset_trans QkTk); rewrite -open_subsetE.
  rewrite -lee_subel_addl//.
  have [_ QkTk /ltW] := TH k.
  apply: le_trans.
  rewrite lee_subel_addl; last first.
    rewrite ge0_fin_numE//.
    have [_ _] := TH k => /lt_le_trans; apply.
    by rewrite leey.
  by rewrite -[in leLHS](setDKU QkTk) (le_trans (outer_measureU2 _ _ _))//= addeC.
pose U := \bigcup_k interior (T k).
have EU : E `<=` U.
  case: EQ => _ /subset_trans; apply.
  by apply: subset_bigcup => k _; exact: QT.
exists U; split => //.
- by apply: bigcup_open => i _; exact: open_interior. (* NB: should be interior_open *)
- apply/andP; split; first exact: le_outer_measure.
  rewrite (splitr e) EFinD addeA.
  apply: (@le_trans _ _ (\big[+%R/0%R]_(0 <= k <oo) mu (Q k) + (e / 2)%:E)%E); last first.
    rewrite leeD2r// ltW//.
    rewrite (le_lt_trans _ muEoo)// le_eqVlt; apply/orP; left; apply/eqP.
    apply: eq_eseriesr => k _.
    rewrite /mu/= /lebesgue_stieltjes_measure/= /measure_extension/=.
    by rewrite measurable_mu_extE//; case: EQ.
  apply: (@le_trans _ _ (\big[+%R/0%R]_(0 <= k <oo) mu (T k))).
    apply: (@le_trans _ _ (mu (\bigcup_k (T k)))).
      apply: le_outer_measure; apply: subset_bigcup => k _.
      exact: interior_subset.
    exact: outer_measure_sigma_subadditive.
  apply: le_trans; last first.
    by apply: epsilon_trick => //; rewrite ltW.
  apply: lee_nneseries => // k _//.
  rewrite -mulrA (_ : _ / _ = 1 / (2 ^+ k.+2))%R; last first.
    by rewrite -invfM// natrX -exprS mul1r.
  by rewrite mul1r; exact: TQ.
Qed.

Lemma lebesgue_regularity_outer_inf_restr (A E : set R) :
  E `<=` A -> (mu E < mu A)%E ->
  mu E = ereal_inf [set mu U | U in [set U | [/\ open U, E `<=` U & U `<=` A]]].
Proof.
move=> EA.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: lb_ereal_inf => /= r /= [B [oB EB BA] <-{r}].
  apply: le_ereal_inf => _ /= [] S_ BS_ <-; exists S_ => //.
  move: BS_ => [mS_ BS_].
  by split; [exact: mS_|exact: (subset_trans EB)].
- apply/lee_addgt0Pr => /= e e0.
  have [U [oU EU /andP[UE UEe]]] := outer_regularity_outer0 E e0.
  apply: ereal_inf_le => /=.
  exists (mu U) => //.
  exists U => //;split => //.
Qed.
*)
End lebesgue_regularity_outer_inf.

Section lebesgue_measurable.
Context {R : realType}.

Let mue := ((@wlength R idfun)^*)%mu.

Definition lebesgue_measurability (E : set R) :=
  forall eps : R, 0 < eps -> exists U, [/\ open U,
  E `<=` U & (mue (U `\` E) <= eps%:E)%E].

(* NB: maybe duplicate lebesgue_regularity_outer *)
Lemma Gdelta_lebesgue_measurability_bounded (E : set R) : Gdelta E ->
  (mue E < +oo%E)%E ->
  lebesgue_measurability E.
Proof.
move=> [] B oB SB mE.
rewrite /lebesgue_measurability => _/posnumP[e] /=.
pose delta_0 (i : nat) : R := (2 ^+ i)^-1.
have delta_0_ge0 (i : nat) : 0 < (2 ^+ i)^-1 :> R by rewrite invr_gt0 exprn_gt0.
pose U_ (k : nat) := projT1 (cid (outer_regularity_outer0 E (delta_0_ge0 k))).
have oU_ k : open (U_ k).
  by rewrite /U_; case: cid => // x/= [].
have EU_ k : E `<=` U_ k.
  by rewrite /U_; case: cid => // x/= [].
have leU_ k : (mue E <= mue (U_ k) <= mue E + (2 ^- k)%:E)%E.
  by rewrite /U_; case: cid => // x/= [].
near \oo => k.
pose Uoo_trunc := \bigcap_(i < k.+1) (U_ i).
exists Uoo_trunc; split.
- exact: bigcap_open.
- exact: sub_bigcap.
- rewrite (_ : mue = lebesgue_measure)//.
  rewrite measureD//=; last 3 first.
    apply: bigcap_measurable.
      by exists 0%N.
    by move=> ? ?; apply: open_measurable.
    rewrite SB.
    apply: bigcap_measurable; first by exists 0%N.
    move=> ? ?.
    by apply: open_measurable.
    rewrite (@le_lt_trans _ _ (mue (U_ 0%N)))//.
      apply: le_outer_measure.
      apply: bigcap_inf.
      near: k.
      by exists 1%N.
    have /andP[_] := leU_ 0%N.
    move=> /le_lt_trans; apply.
    rewrite -exprVn expr0.
    by rewrite lte_add_pinfty// ltry.
  rewrite /Uoo_trunc.
  rewrite lee_subel_addl//.
  rewrite setIidr//; last first.
    by apply: sub_bigcap.
  rewrite (@le_trans _ _ (mue (U_ k)))//.
    apply: le_outer_measure.
    by apply: bigcap_inf => /=.
  have /andP[_] := leU_ k.
  move=> /le_trans; apply.
  rewrite leeD2l// lee_fin -div1r.
  apply/ltW.
  by near: k; exact: near_infty_natSinv_expn_lt.
Unshelve. all: by end_near. Qed.

(* Theorem 1.36 in https://heil.math.gatech.edu/6337/spring11/section1.3.pdf *)
(* TODO: derive lebesgue_measurability from Gdelta *)
Lemma clebesgue_Gdelta_approximation (E : set R) :
  exists H : set _, Gdelta H /\ E `<=` H /\
  (mue E = mue H /\ lebesgue_measurability H).
Proof.
have [Eoo|] := eqVneq (mue E) +oo%E.
  exists setT; split => //; first exact: open_Gdelta openT.
  split => //.
  rewrite Eoo /mue outer_measureT; split => //.
  rewrite /lebesgue_measurability => e e0 /=.
  exists setT; split => //.
    exact: openT.
  by rewrite setDv /mue outer_measure0 lee_fin ltW.
rewrite -ltey -ge0_fin_numE; last exact: outer_measure_ge0.
move=> Efin.
pose delta_0 (i : nat) : R := (2 ^+ i.+1)^-1.
have delta_0_ge0 (i : nat) : 0 < (2 ^+ i.+1)^-1 :> R by rewrite invr_gt0 exprn_gt0.
pose U_ (k : nat) := projT1 (cid (outer_regularity_outer0 E (delta_0_ge0 k))).
have oU_ k : open (U_ k).
  by rewrite /U_; case: cid => // x/= [].
have EU_ k : E `<=` U_ k.
  by rewrite /U_; case: cid => // x/= [].
have leU_ k : (mue E <= mue (U_ k) <= mue E + (2 ^- k.+1)%:E)%E.
  by rewrite /U_; case: cid => // x/= [].
pose Uoo := \bigcap_i (U_ i).
exists Uoo; split.
  by exists U_.
split.
  by apply: sub_bigcap.
have H1 : forall k, (mue E <= mue Uoo <= mue E + (delta_0 k)%:E)%E.
  move=> k.
  apply/andP; split.
    apply: le_outer_measure.
    by apply: sub_bigcap.
  apply: (@le_trans _ _ (mue (U_ k))).
    apply: le_outer_measure.
    by apply: bigcap_inf.
  by have /andP[] := (leU_ k).
split.
  apply/eqP; rewrite eq_le; apply/andP; split.
    apply: le_outer_measure.
    by apply: sub_bigcap.
  apply/lee_addgt0Pr => /= _/posnumP[e].
  rewrite /delta_0 in H1.
  near \oo => k.
  have Ek := H1 k.-1.
  move: Ek => /andP[EUoo UooE].
  rewrite (le_trans UooE)// leeD2l//.
  rewrite lee_fin.
  rewrite -exprVn.
  rewrite -div1r.
  rewrite expr_div_n expr1n.
  rewrite ltW//.
  rewrite prednK; last first.
    by near: k; exists 1%N.
  near: k.
  by apply: near_infty_natSinv_expn_lt.
apply: Gdelta_lebesgue_measurability_bounded.
  rewrite /Gdelta.
  by exists U_.
rewrite (@le_lt_trans _ _ (mue (U_ 0%N)))//.
  apply: le_outer_measure.
  by apply: bigcap_inf.
have /andP[_] := leU_ 0%N.
move=> /le_lt_trans; apply.
rewrite lte_add_pinfty// ?ltry//.
rewrite -ge0_fin_numE//.
exact: outer_measure_ge0.
Unshelve. all: by end_near. Qed.

(*
  ref: https://heil.math.gatech.edu/6337/spring11/section1.2.pdf
  Definition 1.19 defines "Lebesgue measurable" as
  forall e>0, exists open U >= E s.t. |U\E|_e <= e
  the lemma below is the converse of lebesgue_regularity_outer
  (in lebesgue_measure.v)
  except that measurability is Lebesgue-measurability
  which we take here to be Caratheodory-measurability
*)

(*
  ref:https://heil.math.gatech.edu/6337/spring11/section1.2.pdf
  Lemma 1.21
*)
Lemma outer_measure0_measurable (A : set R) :
  mue A = 0 -> lebesgue_measurability A.
Proof.
move=> A0.
(*apply: caratheodory_implies_lebesgue_measurability.
(*apply: regularity_outer_lebesgue.*)
  by rewrite [ltLHS]A0.*)
move=> e e0.
have [U [oU AU]] := outer_regularity_outer0 A e0.
rewrite /lebesgue_measure /=.
rewrite /lebesgue_stieltjes_measure/=.
rewrite /measure_extension/=.
rewrite -/mue.
rewrite A0 add0e => /andP[mU0 mUe].
exists U; split => //.
rewrite (le_trans _ mUe)//.
apply: le_outer_measure.
exact: subDsetl.
Qed.

(* TODO: move *)
Lemma setD_bigcap T (A : set T) (F : (set T)^nat) :
  \bigcap_i F i `\` A = \bigcap_i (F i `\` A).
Proof.
apply/seteqP; split => [x [Fx Ax] k _|x FAx].
  by split => //; apply: Fx.
split; last by have [] := FAx 0%N Logic.I.
by move=> k _; have [] := FAx k Logic.I.
Qed.

Lemma bigcap1 T (F : (set T)^nat) : \bigcap_(i < 1) F i = F 0.
Proof.
apply/seteqP; split => [x H|x H k].
  exact: H.
by rewrite /= ltnS leqn0 => /eqP ->.
Qed.

(* https://heil.math.gatech.edu/6337/spring11/section1.3.pdf *)
(* Theorem 1.37 (a) => (c) *)
Lemma lebesgue_measurability_decomp_Gdelta0 (X E : set R):
  open X -> E `<=` X -> lebesgue_measurability E ->
  exists (U_ : (set R)^nat) (Z : set R),
  [/\ (forall n, U_ n `<=` X /\ open (U_ n)),
    Z `<=` X,
    mue (U_ n) @[n --> \oo] --> mue E,
    mue Z = 0 &
     E = \bigcap_i U_ i `\` Z].
Proof.
move=> oX EX mE/=.
pose delta_0 i : R := (2 ^+ i.+1)^-1.
have delta_0_ge0 i : 0 < (2 ^+ i.+1)^-1 :> R by rewrite invr_gt0 exprn_gt0.
have /= := fun k => (mE _ (delta_0_ge0 k)).
move/choice => [S0 ] /all_and3 [oS0 ES0 mueS0E].
pose U0_ k := (S0 k `&` X).
pose U_ k := \bigcap_(i < k.+1) U0_ i; rewrite /= in U_.
have oU_ k : open (U_ k).
  by apply: bigcap_open => n; exact: openI.
have EU_ k : E `<=` U_ k.
  by apply: sub_bigcap => n/= nk; rewrite subsetI.
have leU_ k : (mue ((U_ k) `\` E) <= (2 ^- k.+1)%:E)%E.
  apply: (@le_trans _ _ (mue (U0_ k `\` E))).
    apply: le_outer_measure.
    by apply: setSD; apply: bigcap_inf => /=.
  apply: (@le_trans _ _ (mue (S0 k `\` E))) => //.
  apply: le_outer_measure.
  by apply: setSD; exact: subIsetl.
have UEcvg0 : mue (U_ i `\` E) @[i --> \oo] --> 0%E.
  apply: (@squeeze_cvge _ _ _ _ (cst 0) _ (fun k => (2 ^- k.+1)%:E)).
  - apply: nearW => n.
    by rewrite leU_ outer_measure_ge0.
   exact: cvg_cst.
  - rewrite (@cvg_shiftS (\bar R) (fun n => (2 ^- n)%:E)).
    apply: cvg_EFin; first by apply: nearW.
    rewrite /comp.
    under eq_cvg do rewrite -exprVn.
    apply: cvg_expr.
    rewrite gtr0_norm.
      rewrite invr_lt1 //.
        by rewrite ltr1n.
      exact: unitf_gt0.
    by rewrite invr_gt0.
pose Z := \bigcap_i (U_ i) `\` E.
exists U_, Z; split.
- move=> n; split.
    rewrite /U_ bigcapIl //.
    by exists 0%N.
  rewrite /U_ bigcapIl; last by exists 0%N.
  by apply: openI => //; exact: bigcap_open.
- apply: (subset_trans (@subDsetl _ _ _)).
  under eq_bigcapr do (rewrite /U_ bigcapIl; last by exists 0%N).
  rewrite bigcapIl; last by exists 0%N.
  exact: subIsetr.
- have [Eoo|] := eqVneq (mue E) +oo%E.
    apply: cvg_near_cst.
    apply/nearW => n.
    apply/eqP; rewrite eq_le Eoo leey/= -Eoo.
    exact: le_outer_measure.
  rewrite -ltey => Elty.
  rewrite (_ : mue = completed_lebesgue_measure) //.
  rewrite (_ : _ E = completed_lebesgue_measure (\bigcap_i U0_ i)); last first.
    rewrite -[LHS]add0e.
    have /cvg_lim <- // := UEcvg0.
    (* ? *)
    have -> : (limn (fun i : nat => mue (U_ i `\` E)) =
        mue (\bigcap_i (U_ i) `\` E)).
      apply/cvg_lim => //=.
      rewrite setD_bigcap.
      have := @nonincreasing_cvg_mu _ _ _ (@lebesgue_measure R) (fun i => U_ i `\` E).
      rewrite (_ : lebesgue_measure = mue)//.
      apply => //.
      + rewrite /U_ bigcap1.
        rewrite /U0_.
        rewrite setDE setIAC -setDE.
        rewrite (@le_lt_trans _ _ (mue (S0 0%N `\` E)))//.
          apply: le_outer_measure.
          exact: subIsetl.
        by rewrite (le_lt_trans (mueS0E _))// ltry.
      + move=> i.
        apply: measurableD.
          by apply: open_measurable.
        admit. (* measurable E *)
      + admit. (* measurable E *)
      + move=> m n mn.
        apply/subsetPset; apply: setSD => x H k h.
        apply: H => //.
        red.
        red in h.
        by rewrite (leq_trans h).
    admit.
  rewrite /U_.
  apply: (@bigcap_cvg_mu _ _ R completed_lebesgue_measure U0_).
      apply: (@le_lt_trans _ _ (mue (S0 0%N))).
        apply: le_outer_measure.
        exact: subIsetl.
      apply: (@le_lt_trans _ _ (mue E + (delta_0 0%N)%:E)%E).
        rewrite -(setUIDK (S0 0%N) E).
        apply: (le_trans (outer_measureU2 mue _ _)).
        rewrite setIidr //.
        by rewrite leeD2l.
      apply: lte_add_pinfty.
        exact: Elty.
      exact: ltey.
    move=> /= n.
    by apply: sub_caratheodory; apply: open_measurable; exact: openI.
  rewrite /=.
  apply: sub_caratheodory.
  apply: Gdelta_measurable.
  by exists U0_ => // n; exact: openI.
- apply/eqP.
  rewrite eq_sym eq_le; apply/andP; split.
    exact: outer_measure_ge0.
  move: (UEcvg0).
  move/cvg_lim => <- //.
  apply: lime_ge.
    by apply/cvg_ex; exists 0.
  apply: nearW => n.
  apply: le_outer_measure.
  apply: setSD.
  exact: bigcap_inf.
- rewrite setDD.
  rewrite eqEsubset; split.
    rewrite subsetI; split; last exact: subset_refl.
    apply: sub_bigcap => n _.
    exact: EU_.
  exact: subIsetr.
Unshelve. all: end_near. Abort.

End lebesgue_measurable.

Section lusinN.
Context {R : realType}.
Let mu := @completed_lebesgue_measure R.

Definition lusinN (A : set R) (f : R -> R) :=
  forall E, E `<=` A -> mu.-cara.-measurable E -> mu E = 0 -> mu (f @` E) = 0.

Definition abs_contN (a b : R) (f : R -> R) :=
  [/\ {within `[a, b]%classic, continuous f},
      bounded_variation a b f &
      lusinN `[a ,b]%classic f].

Fail Lemma lusinN_total_variation a b f : abs_contN a b f ->
  lusinN `[a, b]%classic (total_variation a ^~ f).

Lemma abs_contN_dominates a b (f : cumulative R R) : abs_contN a b f ->
  mu `<< lebesgue_stieltjes_measure f.
Proof.
Abort.

Fail Lemma differentiable_lusinN a b f : {in `]a, b[%classic, differentiable f} ->
  lusinN `]a, b[%classic f.

End lusinN.

Definition preimages_gt1 {R: Type} (X : set R) (Y : set R) (f : R -> R) : set R :=
  Y `&` [set y | (* (X `&` f @^-1` [set y] !=set0) /\ *)
         ~ is_subset1 (X `&` f @^-1` [set y])].

Section preimages_gt1.
Context {R : realType}.

Lemma increasing_preimages_gt1T (X : set R) (f : R -> R) :
  {in X &, nondecreasing_fun f} ->
  {in (X `\` f @^-1` preimages_gt1 X [set: R] f)& , injective f}.
Proof.
move=> ndf.
move=> x y.
rewrite 2!inE => [[Xx + [Xy]]].
rewrite /preimages_gt1/=.
move/not_andP; rewrite not_notE.
rewrite orNp => /(_ Logic.I) Hx.
move/not_andP; rewrite not_notE.
rewrite orNp => /(_ Logic.I) Hy.
move=> fxfy.
apply/eqP.
rewrite eq_le.
rewrite 2!leNgt.
apply/andP; split.
- apply/negP => yx.
  move: fxfy.
  move/eqP; rewrite eq_le; move/andP => [+ fyfx].
  apply/negP; rewrite -ltNge.
  rewrite lt_neqAle; apply/andP; split => //.
  apply/negP; move/eqP => fxfy.
  move: yx.
  rewrite lt_neqAle => /andP[+ yx].
  move/negP.
  case.
  apply/eqP.
  apply/esym.
  by apply: (Hx x y); split.
- apply/negP => yx.
  move: fxfy.
  move/eqP; rewrite eq_le; move/andP => [+ fyfx].
  apply/negP; rewrite -ltNge.
  rewrite lt_neqAle; apply/andP; split => //.
  apply/negP; move/eqP => fxfy.
  move: yx.
  rewrite lt_neqAle => /andP[+ yx].
  move/negP.
  case.
  apply/eqP.
  by apply: (Hy x y); split.
Qed.

End preimages_gt1.

(* cannot make instance for now and maybe useless *)
(* Section total_variation_is_cumulative. *)
(* Variable (R : realType) (a b : R) (f : R -> R). *)
(* Variable (ab : a < b). *)
(* Variable (bvf : bounded_variation a b f). *)
(* Let TV := (fine \o total_variation a ^~ f). *)

(* Let TV_nd : {in `[a, b]&, {homo TV : x y / x <= y}}. *)
(* Proof. *)
(* by apply: TV_nondecreasing. *)
(* Qed. *)

(* Let TV_rc : {in `[a, b], right_continuous f}. *)
(* Proof. *)
(* move=>  *)
(* apply: total_variation_right_continuous. *)

(* HB.instance Definition _ := isCumulative.Build R TV TV_nd TV_rc. *)

(* End total_variation_is_cumulative. *)


(* PR https://github.com/math-comp/analysis/pull/1451 *)

Lemma discontinuityP1 {R : realType} (f : R -> R) (r : R) :
  discontinuity f r -> ~ {for r, continuous f}.
Proof.
rewrite /discontinuity => -[fl fr lr].
move=> /left_right_continuousP [fl' fr'].
have flr : f r = lim (f x @[x --> r^'-]).
  exact/esym/cvg_lim.
have frr : f r = lim (f x @[x --> r^'+]).
  exact/esym/cvg_lim.
move/cvg_ex : fl => [a fa].
have H1 : f r = a.
  exact: (cvg_unique _ fl' fa).
move/cvg_ex : fr => [b fb].
have H2 : f r = b.
  exact: (cvg_unique _ fr' fb).
by move: lr; rewrite -flr -frr eqxx.
Qed.

Lemma discontinuityP2 {R : realType} (f : R -> R) (a b : R) :
  {in `]a, b[ &, nondecreasing_fun f} ->
  forall r, r \in `]a, b[ ->
  ~ {for r, continuous f} ->
  discontinuity f r.
Proof.
move=> ndf r /[dup]rab.
rewrite in_itv/= => /andP[ar rb] ncfr.
have cvgl : cvg (f x @[x --> r^'-]).
  apply: nondecreasing_at_left_is_cvgr; near=> z.
    apply: (itv_sub_in2 _ ndf).
    apply: subset_itvW.
    near: z.
      exact: nbhs_left_ge.
    by rewrite ltW.
  exists (f r) => _ [x xzr <-].
  apply: ndf => //.
    apply: subset_itvW xzr.
    near: z.
      exact: nbhs_left_ge.
    by rewrite ltW.
  by move: xzr; rewrite /= in_itv/= => /andP[_ /ltW].
have cvgr : cvg (f x @[x --> r^'+]).
  admit.
split => //.
apply/negP => /eqP limrl.
apply: ncfr.
apply/left_right_continuousP.
split. (* f r = lim ... by squeeze *)
  admit.
admit.
Abort.

(* Section image_interval_contnuous. *)
(* Context {R : realType}. *)
(* Variables (a b : R). *)
(* Variable F : R -> R. *)
(* Hypothesis ndF : {in `[a, b] &, nondecreasing_fun F}. *)
(* Hypothesis cF : {within `[a, b], continuous F}. *)

(* Lemma image_interval_continuous : exists s : nat -> set R, *)
(*   (forall i, is_interval (s i)) /\ *)
(*   F @` `]a, b[ = \bigcup_i (s i). *)
(* Proof. *)
(* (* nondecreasing_continuous_image_itvoo *) *)

(* End image_interval_contnuous. *)

(* Section image_interval. *)
(* Context {R : realType}. *)
(* Variables (a b : R). *)
(* Variable F : R -> R. *)
(* Hypothesis ndF : {in `[a, b] &, nondecreasing_fun F}. *)

(* Lemma image_interval : exists s : nat -> set R, *)
(*   (forall i, is_interval (s i)) /\ *)
(*   F @` `]a, b[ = \bigcup_i (s i). *)
(* Proof. *)
(* (* split at discontinuities *) *)
(* pose Z := discontinuity F. *)
(* have := discontinuties_countable ndF. *)
(* move/countable_bijP => [N]. *)
(* move/card_set_bijP => /= [invindex bijinvindex]. *)
(* pose index := 'pinv_(fun => b) [set x | x \in `]a, b[ /\ discontinuity F x] invindex. *)
(* Abort. *)

(* End image_interval. *)

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : realType) :=
  Order_isNbhs.Build _ R (@real_order_nbhsE R).

Definition oscillation {R : realType} (f : R -> R) (A : set R) : \bar R :=
  (if A == set0 then
     0
   else
     ereal_sup ((EFin \o f) @` A) - ereal_inf ((EFin \o f) @` A))%E.


Section oscillation_lemma.
Context (R : realType).
Local Open Scope ereal_scope.
Implicit Types (f : R -> R) (A : set R).

Lemma oscillation0 f : oscillation f set0 = 0.
Proof. by rewrite /oscillation eqxx. Qed.

Lemma oscillation_set1 (a : R) f : oscillation f [set a] = 0.
Proof.
rewrite /oscillation ifF; last first.
  by apply/negP/negP/set0P; exists a.
by rewrite !image_set1 ereal_sup1 ereal_inf1 subee.
Qed.

Lemma oscillationN f A : oscillation (\- f)%R A = oscillation f A.
Proof.
rewrite /oscillation; case: ifPn => // A0.
rewrite [X in _ = X - _]ereal_supEN [in X in _ = _ - X]ereal_infEN.
by rewrite [RHS]addeC [in RHS]oppeK setNEFin.
Qed.

Lemma ocsillation_hasNub f A : ~ has_ubound (f @` A) -> oscillation f A = +oo.
Proof.
move=> hasNubA.
rewrite /oscillation; case: ifPn => [/eqP A0|A0].
  absurd: hasNubA; rewrite A0 image_set0 /has_ubound ubound0.
  by apply/set0P; exact: setT0.
rewrite -image_comp (@hasNub_ereal_sup _ (f @` A))//; last first.
  by apply/set0P; contra: A0; exact: image_set0_set0.
rewrite addye//.
apply/eqP; rewrite eqe_oppLRP/= => /ereal_inf_pinfty fA.
move/set0P : A0 => [x Ax].
have := ltry (f x).
by apply/negP; rewrite -leNgt leye_eq; apply/eqP/fA; exists (f x).
Qed.

Lemma ocsillation_hasNlb f A : ~ has_lbound (f @` A) -> oscillation f A = +oo.
Proof.
move=> hasNlbA; have /ocsillation_hasNub : ~ has_ubound ((\- f)%R @` A).
  move/has_ub_lbN.
  rewrite [X in has_lbound X](_ : _ = f @` A)//.
  rewrite image_comp//= (_ : _ \o _ = f)//=.
  by apply/funext => r/=; rewrite opprK.
by rewrite oscillationN.
Qed.

Lemma oscillation_ge0 f A : (0 <= oscillation f A)%E.
Proof.
rewrite /oscillation; case: ifPn => // /set0P[r Ar].
set s : \bar R := ereal_sup _; set i : \bar R := ereal_inf _.
have frsup : ((f r)%:E <= s)%E by rewrite ereal_sup_ubound//=; exists r.
have inffr : (i <= (f r)%:E)%E by rewrite ereal_inf_lbound//=; exists r.
have [sfin|] := boolP (s \is a fin_num).
  have [ifin|] := boolP (i \is a fin_num).
    by rewrite sube_ge0 ?sfin ?ifin// ereal_inf_sup//; exists (f r)%:E, r.
  rewrite fin_numE negb_and !negbK => /predU1P[iy|/eqP iy].
    by rewrite iy addey//; move: sfin; rewrite fin_numE => /andP[].
  by move: inffr; rewrite iy.
rewrite fin_numE negb_and !negbK => /predU1P[sy|/eqP sy].
  by absurd; move/ereal_sup_ninfty : (sy) => /(_ _ (ex_intro2 _ _ _ Ar erefl)).
have [iy|iy] := eqVneq i +oo%E.
  by move: inffr; rewrite iy leye_eq.
by rewrite sy addye// eqe_oppLR.
Qed.

Lemma oscillation_sub f i j :
  i `<=` j -> (oscillation f i <= oscillation f j)%E.
Proof.
move=> ij; have [->|i0] := eqVneq i set0.
  by rewrite oscillation0 oscillation_ge0.
have [j0|j0] := eqVneq j set0.
  by move: ij; rewrite j0 subset0 => /eqP; rewrite (negbTE i0).
rewrite /oscillation (negbTE i0) (negbTE j0) leeB//.
- by apply: ereal_sup_le; exact: image_subset.
- by apply: ereal_inf_le_tmp; exact: image_subset.
Qed.

End oscillation_lemma.


Section cplt_hull.
Context {R : realType}.
Implicit Type (A : set R).

(* complement hull? *)
Definition cplt_hull A := [set` Rhull A] `\` A.

Lemma cplt_hull0 A : is_interval A -> cplt_hull A = set0.
Proof.
by move=> itvA; rewrite /cplt_hull -((is_intervalP A).1 itvA) setDv.
Qed.

Lemma cplt_hull_set0 : cplt_hull set0 = set0.
Proof. by rewrite cplt_hull0. Qed.

Lemma cplt_hullT : cplt_hull setT = set0.
Proof. by rewrite cplt_hull0. Qed.

Lemma cplt_hull_subset_Rhull A : cplt_hull A `<=` [set` Rhull A].
Proof. exact: subDsetl. Qed.

(* NB: PR in progress *)
Lemma not_nonemptyP A : ~ (A !=set0) <-> A = set0.
Proof. by split; [|move=> ->]; move/set0P/negP; [move/negbNE/eqP|]. Qed.

Lemma has_ubound_cplt_hull A :
  has_ubound A -> has_ubound (cplt_hull A).
Proof.
move=> /[dup]/asboolP u [ub ubAub]; exists ub => x [+ _].
have [|/=/contrapT A0] := pselect (~ (A !=set0)).
  by move/not_nonemptyP ->; rewrite RhullK ?inE.
by rewrite in_itv/= u => /andP[_]/lteifW/le_trans; apply; exact: ge_sup.
Qed.

Lemma has_lbound_cplt_hull A :
  has_lbound A -> has_lbound (cplt_hull A).
Proof.
move=> /[dup]/asboolP l [lb lbAlb]; exists lb => x [+ _].
have [/= A0|] := pselect (A !=set0); last first.
  by move/set0P/negP/negbNE/eqP => ->; rewrite Rhull0 set_itvoo0.
rewrite in_itv/= l => /andP[+ _] => /lteifW; apply: le_trans; exact: lb_le_inf.
Qed.

Lemma cplt_hull_complement A : cplt_hull A `<=` ~` A.
Proof. rewrite /cplt_hull; exact: subDsetr. Qed.

(* unused *)
Lemma cplt_hull_sup A : has_ubound A -> ~ (cplt_hull A) (sup A).
Proof.
move=> ubA; rewrite /cplt_hull/= in_itv/= andC -implypN => Asup.
by move/asboolPn: (Asup); move/asboolP: (ubA) => -> -> /=; rewrite ltxx andbF.
Qed.

(* notable property of cplt_hull *)
(*
Lemma rray_has_ubound_cplt_hull A :
  A \in (nbhs +oo) -> has_ubound (cplt_hull A).
Proof.
rewrite inE.
move=> [b [_ Hb]].
Abort.
*)

Lemma cplt_hull_lt_sup A :
  has_ubound A -> cplt_hull A `<=` [set x | x < sup A].
Proof.
move=> hasubA x [/= + nAx].
rewrite in_itv/=; move/andP => [_]; rewrite ifT; last by exact/asboolP.
have [/asboolP/= ?|//] := boolP `[< A (sup A)>];
by rewrite le_eqVlt => /predU1P[|//] => ?; subst.
Qed.

(* unused *)
Lemma cplt_hull_inf A :
  has_lbound A -> ~ (cplt_hull A) (inf A).
Proof.
move=> haslbA.
rewrite /cplt_hull/=.
apply/not_andP.
rewrite orpN => Ainf.
have gt_inf := inf_lb_strict haslbA Ainf.
rewrite in_itv/=.
case: ifP; move/asboolP => //= _.
move/asboolPn/negPf : Ainf => -> /=.
by rewrite ltxx.
Qed.

Lemma inf_lt_cplt_hull A :
  has_lbound A -> cplt_hull A `<=` [set x | inf A < x].
Proof.
move=> haslbA x [/= + nAx].
rewrite in_itv/=.
move/andP => [+ _]; move/asboolP : (haslbA) => ->.
have [|/asboolF -> //] := pselect (A (inf A)).
move=> /[dup]/asboolP -> AinfA/=.
rewrite le_eqVlt => /orP[|//]; move/eqP => xinfA.
by move: nAx; rewrite -xinfA.
Qed.

Lemma cplt_hullEitvoo A :
  has_ubound A -> has_lbound A ->
  cplt_hull A = `]inf A, sup A[ `&` ~` A.
Proof.
move/[dup]/cplt_hull_lt_sup => ciAsup hasubA.
move/[dup]/inf_lt_cplt_hull => ciAinf haslbA.
rewrite eqEsubset; split.
- move=> x ciA/=; split.
  + rewrite in_itv/=; apply/andP; split.
    * exact: ciAinf.
    * exact: ciAsup.
  + by move: ciA; rewrite /cplt_hull/= => -[].
rewrite /cplt_hull setDE; apply: setSI.
rewrite/Rhull.
move: hasubA haslbA => /asboolP -> /asboolP ->.
case: `[< A (inf A) >]; case: `[< A (sup A) >] => //=.
- exact: subset_itv_oo_cc.
- exact: subset_itv_oo_co.
- exact: subset_itv_oo_oc.
Qed.

Lemma cplt_hullEitvyo A :
  has_ubound A -> ~ has_lbound A ->
  cplt_hull A = `]-oo, sup A[ `&` ~` A.
Proof.
move/[dup]/cplt_hull_lt_sup => ciAsup hasubA.
move=> hasNlbA.
rewrite /cplt_hull.
rewrite /Rhull.
move/asboolP : (hasubA) => ->.
move/asboolF : (hasNlbA) => -> /=.
have [Asup|nAsup] := pselect (A (sup A)).
  move/asboolP : (Asup) => ->/=.
  rewrite -(setUitv1 true)// setDUl -[RHS]setU0; congr setU.
  rewrite setD_eq0.
  by rewrite sub1set inE.
by move/asboolF : nAsup => ->.
Qed.

Lemma cplt_hullEitvoy A :
  ~ has_ubound A -> has_lbound A ->
  cplt_hull A = `]inf A, +oo[ `&` ~` A.
Proof.
move=> hasNubA.
move/[dup]/inf_lt_cplt_hull => ciAinf haslbA.
rewrite /cplt_hull.
rewrite /Rhull.
move/asboolP : (haslbA) => ->.
move/asboolF : (hasNubA) => -> /=.
have [Ainf|nAinf] := pselect (A (inf A)).
  move/asboolP : (Ainf) => ->/=.
  rewrite -(setU1itv false)// setDUl -[RHS]set0U; congr setU.
  rewrite setD_eq0.
  by rewrite sub1set inE.
by move/asboolF : nAinf => ->.
Qed.

Lemma cplt_hull_unboundEitvoo A :
  A !=set0 -> ~ has_ubound A -> ~ has_lbound A ->
  cplt_hull A = ~` A.
Proof.
move=> [x Ax].
move=> hasNubA hasNlbA.
rewrite -setTD; congr setD.
rewrite/Rhull.
move/asboolF : hasNlbA => ->.
move/asboolF : hasNubA => ->.
exact: interval_unbounded_setT.
Qed.

Let compact_open_complement A : compact A -> open (cplt_hull A).
Proof.
move=> cpA.
have := compact_bounded cpA.
move=> -[bnd [_ bndA]].
rewrite cplt_hullEitvoo; last 2 first.
- exists (bnd + 1) => x Ax.
  rewrite ler_normlW//.
  apply: bndA => //.
  by rewrite ltrDl.
- exists (- (bnd + 1)) => x Ax.
  rewrite lerNnormlW//.
  apply: bndA => //.
  by rewrite ltrDl.
apply: openI => //.
apply: closed_openC.
exact: (compact_closed _ cpA).
Qed.

Lemma closed_open_cplt_hull A : closed A -> open (cplt_hull A).
Proof.
move=> cA.
have [ubA|ubA] := pselect (has_ubound A).
- have [lbA|lbA] := pselect (has_lbound A).
  + rewrite cplt_hullEitvoo//.
    by apply: openI => //; rewrite openC.
  + rewrite cplt_hullEitvyo//.
    by apply: openI => //; rewrite openC.
- have [lbA|lbA] := pselect (has_lbound A).
  + rewrite cplt_hullEitvoy//.
    by apply: openI => //; rewrite openC.
  + have [A0|/set0P/negP/negPn/eqP ->] := pselect (A !=set0).
      by rewrite cplt_hull_unboundEitvoo// openC.
    by rewrite cplt_hull_set0.
Qed.

End cplt_hull.

(* TODO *)
Definition cont_itv1 {R : realType} (A : set R) (s_ : R^nat) :=
  fun k => Num.min (sup A) (s_ k.-1).

Definition cont_itv2 {R : realType} (A : set R) (i_ : R^nat) :=
  fun k => Num.max (i_ k) (inf A).

Definition cont_itvs {R : realType} (A : set R) (i_ s_ : R^nat) : (set R)^nat :=
  fun k => [set` `[cont_itv1 A s_ k, cont_itv2 A i_ k]].

Section cont_itvs.
Context {R : realType}.
Variables A : set R.

Lemma cont_itvsS i_ s_ k :
  (forall k, i_ k \in `[inf A, sup A]) ->
  (forall k, s_ k \in `[inf A, sup A]) ->
  cont_itvs A i_ s_ k `<=` `[inf A, sup A].
Proof.
move=> icd scd r.
rewrite /cont_itvs /cont_itv1 /cont_itv2/=.
rewrite !in_itv/= => /andP[H1 H2].
apply/andP; split.
Abort.

End cont_itvs.

(* NB: A is supposed to be a perfect set so that A is closed *)
Definition contiguous_intervals {R : realType} (A : set R) : (set R)^nat :=
  match pselect (closed A) with
  | left H => open_disjoint_itv (closed_open_cplt_hull H)
  | right _ => cst set0
  end.

Definition contiguous_intervals1 {R : realType} (A : set R) : R^nat :=
  fun n => inf (contiguous_intervals A n).

Definition contiguous_intervals2 {R : realType} (A : set R) : R^nat :=
  fun n => sup (contiguous_intervals A n).

Lemma is_subset1_set1 {R : realType} (A : set R) : A !=set0 -> is_subset1 A ->
  A = [set xget point A].
Proof.
move=> A0 A1.
case: xgetP => /= [_ -> Aget|].
  apply/seteqP; split => [x Ax/=|x/= ->//].
  exact: A1.
by case: A0 => s As /(_ s).
Qed.

(* TODO: move near has_bound_not_subset1_inf_sup in absolute_continuity.v *)
Lemma has_bound_inf_sup {R : realType} (A : set R) :
  has_lbound A -> has_ubound A -> (inf A <= sup A)%R.
Proof.
have [-> _ _|/set0P A0 lbA ubA] := eqVneq A set0; first by rewrite inf0 sup0.
have [|/has_bound_not_subset1_inf_sup] := pselect (is_subset1 A); last first.
  by move=> /(_ lbA ubA) /ltW.
move/is_subset1_set1 => /(_ A0) ->.
by rewrite inf1 sup1.
Qed.

Section contiguous_intervals_lemmas.
Context {R : realType}.
Implicit Type (A : set R).

Lemma open_contiguous_intervals A n : open (contiguous_intervals A n).
Proof.
rewrite /contiguous_intervals; case: pselect => cA//.
exact: open_disjoint_itv_open.
Qed.

Lemma is_interval_contiguous_intervals A n :
  is_interval (contiguous_intervals A n).
Proof.
rewrite /contiguous_intervals; case: pselect => cA//.
exact: open_disjoint_itv_is_interval.
Qed.

Lemma disjoint_contiguous_intervals A :
  trivIset [set: nat] (contiguous_intervals A).
Proof.
rewrite /contiguous_intervals; case: pselect => cA//.
  exact: open_disjoint_itv_trivIset.
exact: trivIset_set0.
Qed.

Lemma bigcup_contiguous_intervals A :
  closed A -> cplt_hull A = \bigcup_k (contiguous_intervals A) k.
Proof.
move=> cA.
rewrite /contiguous_intervals; case: pselect => ? //.
by rewrite -open_disjoint_itv_bigcup.
Qed.

Lemma contiguous_intervals_subsetC A n :
  contiguous_intervals A n `<=` ~` A.
Proof.
rewrite /contiguous_intervals; case: pselect => cA//=.
apply: (@subset_trans _ (cplt_hull A)); last first.
  exact: cplt_hull_complement.
rewrite [in X in _ `<=` X](open_disjoint_itv_bigcup (closed_open_cplt_hull cA)).
exact: bigcup_sup.
Qed.

Lemma contiguous_intervalsS A n :
  contiguous_intervals A n `<=` cplt_hull A.
Proof.
have [cA|cA] := pselect (closed A).
  by rewrite (bigcup_contiguous_intervals cA); exact: bigcup_sup.
(* NB: needs lemma here *)
by rewrite /contiguous_intervals; case: pselect.
Qed.

Lemma has_lbound_contiguous_intervals A :
  has_lbound A -> forall n, has_lbound (contiguous_intervals A n).
Proof.
move/inf_lt_cplt_hull => lbA i; exists (inf A) => r.
by move/contiguous_intervalsS/lbA => /= /ltW.
Qed.

Lemma has_ubound_contiguous_intervals A :
  has_ubound A -> forall n, has_ubound (contiguous_intervals A n).
Proof.
move/cplt_hull_lt_sup => lbA i; exists (sup A) => r.
by move/contiguous_intervalsS/lbA => /= /ltW.
Qed.

(*Lemma contiguous_intervals1_fin_num A : has_lbound A ->
 forall n, contiguous_intervals1 A n \is a fin_num.
Proof.
move=> + i.
move/has_lbound_contiguous_intervals => /(_ i) lbA.
rewrite /contiguous_intervals1 /Rhull; case: ifPn => //=.
by move/asboolP.
Qed.

Lemma contiguous_intervals2_fin_num A : has_ubound A ->
 forall i, contiguous_intervals2 A i \is a fin_num.
Proof.
move=> + i.
move/has_ubound_contiguous_intervals => /(_ i) ubA.
rewrite /contiguous_intervals2 /Rhull; case: ifPn => /=; case: ifPn => //.
  by move/asboolP.
by move/asboolP.
Qed.*)

Lemma contiguous_intervals1_le_contiguous_intervals2 A n :
  has_lbound A ->
  has_ubound A ->
  (contiguous_intervals1 A n <= contiguous_intervals2 A n)%R.
Proof.
move=> ? ?.
rewrite /contiguous_intervals1 /contiguous_intervals2.
rewrite has_bound_inf_sup//.
  exact: has_lbound_contiguous_intervals.
exact: has_ubound_contiguous_intervals.
Qed.

Lemma bigcup_contiguous_intervals_fine A :
  compact A -> cplt_hull A =
      \bigcup_k `](contiguous_intervals1 A k),
                  (contiguous_intervals2 A k)[%classic.
Proof.
move=> cA.
have closedA : closed A by exact: compact_closed.
rewrite bigcup_contiguous_intervals//.
apply: eq_bigcupr => n _.
transitivity [set` Rhull (contiguous_intervals A n)].
  by rewrite RhullK//; rewrite inE; exact: is_interval_contiguous_intervals.
have haslbA : has_lbound A.
  apply: bounded_has_lbound.
  exact: compact_bounded.
have hasubA : has_ubound A.
  apply: bounded_has_ubound.
  exact: compact_bounded.
have [haslbciA hasubciA citvAinf citvAsup] :
  [/\ has_lbound (contiguous_intervals A n),
       has_ubound (contiguous_intervals A n),
       ~ contiguous_intervals A n (inf (contiguous_intervals A n))&
       ~ contiguous_intervals A n (sup (contiguous_intervals A n))].
  split.
  - exact: has_lbound_contiguous_intervals.
  - exact: has_ubound_contiguous_intervals.
  - apply: open_haslb_memNinf.
    + exact: has_lbound_contiguous_intervals.
    + exact: open_contiguous_intervals.
  - apply: open_hasub_memNsup.
    + exact: has_ubound_contiguous_intervals.
    + exact: open_contiguous_intervals.
rewrite /contiguous_intervals1/contiguous_intervals2/Rhull/=.
move/asboolP: haslbciA ->; move/asboolP: hasubciA ->.
by move/asboolF: citvAinf ->;move/asboolF: citvAsup ->.
Qed.

Lemma fine_contiguous_intervals1 A : (*compact A ->*)
  forall i, contiguous_intervals1 A i = inf (contiguous_intervals A i).
Proof. by []. Qed.

Lemma fine_contiguous_intervals2 A : (*compact A ->*)
  forall i, contiguous_intervals2 A i = sup (contiguous_intervals A i).
Proof. by []. Qed.

(* unused *)
Lemma contiguous_ooitv A :
  has_ubound A -> has_lbound A ->
  forall i, (contiguous_intervals A i) =
   `]contiguous_intervals1 A i, contiguous_intervals2 A i[%classic.
Proof.
move=> /[dup] hasubA [u Au] /[dup] haslbA [l Al] i.
rewrite /contiguous_intervals1/contiguous_intervals2.

rewrite -{1}(@RhullK _ (contiguous_intervals A i)); last first.
  by rewrite inE; exact: is_interval_contiguous_intervals.

rewrite /Rhull.
rewrite 2?ifT/=; last 2 first.
- exact/asboolP/has_ubound_contiguous_intervals.
- exact/asboolP/has_lbound_contiguous_intervals.
have : ~ contiguous_intervals A i(inf (contiguous_intervals A i)).
   apply: open_haslb_memNinf.
    exact: has_lbound_contiguous_intervals.
  exact: open_contiguous_intervals.
have : ~ contiguous_intervals A i (sup (contiguous_intervals A i)).
  apply: open_hasub_memNsup.
    exact: has_ubound_contiguous_intervals.
  exact: open_contiguous_intervals.
by move=> /asboolF -> /asboolF ->//=.
(* lemma? *)
(*rewrite eqEsubset; split.
  by move=> z [x/= + <-]; rewrite 2!in_itv/= 2!lte_fin.
move=> z/=; rewrite in_itv/= => /andP[infz zsup].
have finz : z \is a fin_num.
  rewrite fin_numElt; apply/andP; split.
  - by apply: lt_trans infz; rewrite ltNyr.
  - by apply: (lt_trans zsup); rewrite ltry.
move: infz zsup.
move/EFin_fin_numP : finz => [x ->]; rewrite 2!lte_fin => infx xsup.
by exists x => //; rewrite in_itv/= infx xsup.*)
Qed.

End contiguous_intervals_lemmas.

Lemma finite_seqP_new {T : eqType} A :
   finite_set A <-> exists2 s : seq T, uniq s & A = [set` s].
Proof.
elim/eqPchoice: T => T in A *; rewrite finite_fsetP.
split=> [[X ->]|[s us ->]]; first by exists X.
by exists [fset x | x in s]%fset; apply/seteqP; split=> x /=; rewrite inE.
Qed.

Section lemmas_for_contiguous_intervals_support.
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

Lemma sort_sorted_fst_iota (p : seq (R * R)) n :
  let le1 := (fun x y : R * R => x.1 <= y.1) in
  sorted le1 p ->
  size p = n ->
  sorted <=%R [seq (p`_i).1 | i <- iota 0 n].
Proof.
move=> le1 le1p pn.
rewrite (map_comp fst).
rewrite sorted_map.
rewrite -/lt1 -pn.
by rewrite map_nth_iota ?subn0// drop0 take_size.
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

Lemma set1_not_open (x : R) : ~ open [set x].
Proof. by rewrite openE/= interior_set1 => /(_ x); exact. Qed.

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
  move/is_subset1_set1 => /(_ Zj0)Zj1.
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

Lemma contiguous_intervals2_notin (Z : set R) : has_ubound Z -> forall j,
  ((contiguous_intervals2 Z j))
    \notin `]contiguous_intervals1 Z j, contiguous_intervals2 Z j[.
Proof.
move=> ubZ j.
rewrite in_itv/=.
by rewrite ltxx andbF.
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

(* duplicate nth_map? *)
Lemma fst_map {T1 T2} (l : seq (T1 * T2)) d1 d2 i :
   (i < size l)%N ->
  (nth (d1, d2) l i).1 = nth d1 (map fst l) i.
Proof. by move=> ?; rewrite (nth_map (d1, d2)). Qed.

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
  move/is_subset1_set1 => /(_ Zj0)Zj1.
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

Lemma contiguous_intervals1_notin (Z : set R) : has_lbound Z -> forall j,
  ((contiguous_intervals1 Z j))
    \notin `]contiguous_intervals1 Z j, contiguous_intervals2 Z j[.
Proof.
move=> lbZ j.
rewrite in_itv/=.
by rewrite ltxx/=.
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

End lemmas_for_contiguous_intervals_support.

Section contiguous_intervals_support.
Context {R : realType}.

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
  [set` p] `<=` contiguous_intervals_support P ->
  sorted <=%R [seq contiguous_intervals1 P j | j <- p] ->
  sorted <=%R [seq contiguous_intervals2 P j | j <- p].
Proof.
case: p => // h t lbP ubP Pp sorted1.
apply/(sortedP 0) => i.
rewrite size_map [in X in X -> _]/= ltnS => ti.
rewrite (nth_map 0)//; last by rewrite /= ltnW.
rewrite (nth_map 0)//.
apply: contiguous_intervals_sort' => //.
  move: Pp => /(_ t`_i)/=.
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

Lemma contiguous_infinite (a b : R) (P : set R) :
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
    move/is_subset1_set1 => /(_ P0)Pr.
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
    rewrite sort_sorted_fst_iota//; last first.
      by rewrite /sorted_bnds size_sort size_map.
    by apply: sort_sorted; exact: total_le1.
  rewrite (@setD_bigcup_itvoo _ _ _ (fun k => (sorted_bnds`_k).1)
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
    by rewrite Pp.
    by rewrite -qE1.
  - move=> i pi.
    have ? : (i < size p)%N by rewrite (leq_trans pi)// leq_pred.
    have ? : (i.+1 < size p)%N by rewrite -(@prednK (size p)) ?lt0n ?size_eq0.
    have H2 : (sorted_bnds`_i).1 <= (sorted_bnds`_i.+1).1.
      rewrite fst_map; last by rewrite size_sort size_map.
      rewrite fst_map; last by rewrite size_sort size_map.
      apply: le_sorted_leq_nth => //; last 2 first.
      - by rewrite inE size_map size_sort size_map (leq_trans pi)// leq_pred.
      - by rewrite inE/= size_map size_sort size_map.
      rewrite sorted_map.
      apply: sort_sorted => x y.
      exact: le_total.
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

Lemma contiguous_intervals_support0 (Z : set R) :
  ~ (closed Z) ->
  contiguous_intervals_support Z = set0.
Proof.
move=> ncZ.
rewrite /contiguous_intervals_support.
rewrite -set_false.
apply: eq_set => x; rewrite inE.
rewrite propeqE falseE; split => //.
move/set0P/negP; apply/negP/eqP.
rewrite /contiguous_intervals.
by case : (pselect (closed Z)).
Qed.

Lemma contiguous_intervals_nonempty (Z : set R) :
  Z != setT ->
   contiguous_intervals_support Z !=set0 -> Z !=set0.
Proof.
move=> nZT [n [x cgitvZx]].
have cZ : closed Z.
  apply: contrapT => /contiguous_intervals_support0.
  by apply/eqP/negP/negP/set0P; exists n; exists x.
apply/set0P/negP => /eqP Z0.
have : cplt_hull Z !=set0.
  rewrite bigcup_contiguous_intervals//.
  exists x; exists n => //.
apply/set0P/negP/negPn/eqP; rewrite Z0; exact: cplt_hull0.
Qed.

Lemma contiguous_intervals_set0 (i : nat) :
  @contiguous_intervals R set0 i = set0.
Proof.
apply/eqP/not_notP; move/negP/set0P => -[x i0].
have := @cplt_hull_set0 R.
move/eqP; apply/negP/set0P.
exists x.
rewrite bigcup_contiguous_intervals; last exact: closed0.
by exists i.
Qed.

Lemma contiguous_intervals_support_not_subset1 (Z : set R) n :
  contiguous_intervals_support Z n ->
  ~ is_subset1 (contiguous_intervals Z n).
Proof.
move/(is_subset1_set1) => H /H {}H.
apply: (@set1_not_open _ (xget point (contiguous_intervals Z n))).
rewrite -H.
exact: open_contiguous_intervals.
Qed.

Lemma contiguous_support_bnd_lt (Z : set R) (i : nat) :
  compact Z ->
  contiguous_intervals_support Z i ->
  contiguous_intervals1 Z i < contiguous_intervals2 Z i.
Proof.
move=> cZ.
rewrite /contiguous_intervals_support/= => cgiZ0.
have [Z0|Z0] := pselect (Z !=set0); last first.
  have {}Z0 : Z = set0 by apply/eqP/not_notP; move/negP/set0P.
  move: cgiZ0; rewrite Z0 contiguous_intervals_set0.
  by move/set0P/negP.
apply: has_bound_not_subset1_inf_sup.
- apply: (@subset_has_lbound _ _ _ ([set` Rhull Z])).
    apply: (subset_trans (@contiguous_intervalsS _ _ _)).
    exact: cplt_hull_subset_Rhull.
- rewrite (compact_Rhull cZ Z0).
  exact: has_lbound_itv.
- move: cZ; rewrite Rcompact_boundE => -[_ ubZ lbZ].
  rewrite (contiguous_ooitv ubZ lbZ).
  exact: has_ubound_itv.
exact: contiguous_intervals_support_not_subset1.
Qed.

End contiguous_intervals_support.
