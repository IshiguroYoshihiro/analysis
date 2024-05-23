From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
Require Import set_interval.
Require Import signed reals ereal topology normedtype sequences real_interval.
Require Import esum measure lebesgue_stieltjes_measure lebesgue_measure numfun.
Require Import realfun exp derive.

(**md**************************************************************************)
(* # Absolute Continuity                                                      *)
(* ```                                                                        *)
(*   Gdelta (S ; set R) == S is a set of countable intersection of open sets  *)
(*   abs_cont ==                                                              *)
(* ```                                                                        *)
(* ref: An Elementary Proof of the Banach–Zarecki Theorem                     *)
(******************************************************************************)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

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

Section move_to_realfun.
Context {R : realType}.

(* TODO:PR *)
Lemma bigcap_open (F : (set R) ^nat) :
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
move/(_ (lt_trans ar rb)) => [cf [fa fb]].

move : fa.
move/cvg_at_rightP.
move/(_ (fun n => a + 2^-1 ^ n.+1)).
have H : ((forall n : nat, a < (a + 2^-1 ^ n.+1)%E) /\ (a + 2^-1 ^ n.+1)%E @[n --> \oo] --> a).
  admit.
move/(_ H) => {H}.
have H : (f (a + 2^-1 ^ n.+1)%E - f a) @[n --> \oo] --> 0%R.
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
have [cabf [fa fb]] := (continuous_within_itvP f (lt_trans ar rb)).1 cf.
rewrite in_itv/=; apply/andP; split.
  move: (fa) => /cvg_lim <-//.
  apply: limr_le.
  - apply/cvg_ex.
    exists (f a).
    exact: fa.
  - near=> a0.
    apply: ndf.
    rewrite in_itv/=; apply/andP; split => //.
    rewrite (le_lt_trans _ rb)//.
    near: a0.
    by apply: nbhs_right_le.
    by rewrite in_itv/= ar.
    near: a0.
    by apply: nbhs_right_le.
move: (fb) => /cvg_lim <-//.
apply: limr_ge.
- apply/cvg_ex.
  exists (f b).
  exact: fb.
- near=> b0.
  apply: ndf.
  by rewrite in_itv/= ar.
  rewrite in_itv/=; apply/andP; split => //.
  by rewrite (lt_trans ar)//.
  near: b0.
  by apply: nbhs_left_ge.
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

(* #PR1221 *)
Lemma not_near_at_leftP T (f : R -> T) (p : R) (P : pred T) :
  ~ (\forall x \near p^'-, P (f x)) ->
  forall e : {posnum R}, exists2 x : R, p - e%:num < x < p & ~ P (f x).
Proof.
Admitted.

Lemma nondecreasing_bound_le (a : R) (b : itv_bound R) (f : R -> R) :
  ((BLeft a) < b)%O ->
  {in (Interval (BLeft a) b) &, {homo f : x y / (x <= y)%O}} ->
  f x @[x --> a^'+] --> f a ->
  forall x, a < x -> f a <= f x.
Proof.
case: b.
case => t.
Abort.

Lemma continuous_in_nondecreasing_oo_cc (a b : R) (f : R -> R) : a < b ->
  {within `[a, b] , continuous f} ->
  {in `]a, b[ &, {homo f : x y / (x <= y)%O}} ->
  {in `[a, b] &, {homo f : x y / (x <= y)%O}}.
Proof.
move=> ab cf ndf.
have [cf' [fxa fxb]] := (continuous_within_itvP f ab).1 cf.
move=> r x.
rewrite !in_itv/=.
have faz z : a < z -> z <= b -> f a <= f z.
  move=> az zb.
  move: (fxa).
  move/cvg_lim => <- //.
  rewrite limr_le //.
    by apply: cvgP fxa.
  near=> y.
  move: zb.
  rewrite le_eqVlt.
  move/predU1P => [-> |zb].
    move: (fxb).
    move/cvg_lim => <- //.
    rewrite limr_ge //.
      by apply: cvgP fxb.
    near=> b0.
    apply: ndf.
     - by rewrite ?in_itv/=; apply/andP.
     - by rewrite ?in_itv/=; apply/andP.
     near: b0.
     by apply: nbhs_left_ge.
  apply: ndf => //.
      rewrite in_itv /=.
      by apply/andP.
    by rewrite in_itv/= az.
  near: y.
  by apply: nbhs_right_le.
have fzb z : a < z -> z < b -> f z <= f b.
  move=> az zb.
  move: (fxb).
  move/cvg_lim => <- //.
  apply: limr_ge.
    by apply: cvgP fxb.
  near=> y.
  apply: ndf.
  - by rewrite ?in_itv/=; apply/andP.
  - by rewrite ?in_itv/=; apply/andP.
  near: y.
  by apply: nbhs_left_ge.
move => /andP[].
rewrite le_eqVlt.
move=> /predU1P[<- |].
  move=> _ /andP[_].
  rewrite le_eqVlt.
  move/predU1P => [-> _|xb].
    by apply: faz => //.
  rewrite le_eqVlt.
  move/predU1P => [-> //| ax].
  apply: faz => //.
  by rewrite ltW.
move=> ar.
move=> _ /andP[_].
rewrite le_eqVlt.
move=> /predU1P[-> //|].
  rewrite le_eqVlt.
  move/predU1P => [-> //|rb].
  by apply: fzb.
move=> xb rx.
have ax : a < x by apply: lt_le_trans rx.
have rb : r < b by apply: le_lt_trans xb.
by apply: ndf => //; rewrite in_itv/= ?ar ?ax.
Unshelve. all: by end_near. Qed.

Lemma nondecreasing_lim_le (a : R) (f : R -> R) :
  \forall x \near a^'+, {homo f : x y / (x <= y)%O} ->
  f x @[x --> a^'+] --> f a ->
  \forall x \near a^'+, f a <= f x.
Abort.

Lemma near_right_in_itvoo (a b : R) (x y : bool) :
  \forall r \near a^'+, r \in (Interval (BSide x a) (BSide y b)).
Abort.

Lemma continuous_nondecreasing_image_itvoo_itv (a b : R) (f : R -> R) : a < b ->
  {within `[a, b] , continuous f} ->
  {in `]a, b[ &, {homo f : x y / (x <= y)%O}} ->
exists b0 b1,
  f @` `]a, b[%classic = [set x | x \in (Interval (BSide b0 (f a)) (BSide b1 (f b)))].
Proof.
move=> ab cf ndf.
have ndfcc := continuous_in_nondecreasing_oo_cc ab cf ndf.
have [cf' [fxa fxb]] := (continuous_within_itvP f ab).1 cf.
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

Lemma integral_continuous_nondecreasing_itv
(a b : R) (f : R -> R) :
  (a < b) ->
  {within `[a, b] , continuous f} ->
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
move/orP; case.
- move/eqP => fafb.
  rewrite ifF.
    by rewrite fafb -EFinB subrr.
  rewrite lte_fin.
  rewrite lt_neqAle.
  rewrite fafb.
  by rewrite eq_refl.
- by rewrite lte_fin => ->.
Qed.

(* move to realfun.v? *)
Lemma continuous_decreasing_image_itvoo (a b : R) (f : R -> R) :
  {within `[a, b] , continuous f} ->
  {in `[a, b] &, {homo f : x y /~ (x < y)%O}} ->
  f @` `]a, b[%classic = `]f b, f a[%classic.
Proof.
case : (leP a b) => [|ba].
  rewrite le_eqVlt.
  case/orP.
    by move/eqP ->; rewrite !set_itvoo0 image_set0 => _ _.
  move=> ltab cf ndf.
Admitted.

End move_to_realfun.

Section image_of_itv.
Context (R : realType).
Implicit Type (f : R -> R) (a b: R).

Local Notation mu := (@lebesgue_measure R).

Let closure_itvoo (a b : R) :
closure `]a, b[%classic = `[a, b]%classic.
Proof.
rewrite closure_limit_point.
rewrite eqEsubset; split.


(* have -> : `]a, b[ `|` limit_point `]a, b[%classic = limit_point `]a, b[%classic. *)
(*   apply/setUidPr. *)
(*   move=> x /=. *)
(*   rewrite in_itv/=. *)
(*   move/andP => [ax xb]. *)
(*   move=> /= S. *)
(*   rewrite nbhs_nearE => nearS. *)
(*   near x^' => y. *)
(*   exists y; split. *)
(*       near: y. *)
(*       exact: nbhs_dnbhs_neq. *)
(*     rewrite in_itv/=. *)
(*     apply/andP; split. *)
      

(*       near: y. *)
(*       rewrite near_nbhs. *)
(*       apply: nbhs_right_lt. *)
(* rewrite setUS. *)
(* rewrite eqEsubset. *)
Admitted.

Lemma closure_itv (a b : R) (x y : bool) : a < b ->
closure [set` (Interval (BSide x a) (BSide y b))] = `[a, b]%classic.
Proof.
move=> ab.
rewrite eqEsubset; split.
  rewrite set_itv_splitI.
  move=> r.
  move/closureI.
  have -> : closure [set` Interval (BSide x a) +oo%O] = `[a, +oo[%classic.
    case: x.
      apply/esym.
      apply/closure_id.
      rewrite set_itv_c_infty.
      exact: closed_ge.
    rewrite set_itv_o_infty set_itv_c_infty.
    by rewrite closure_gt.
  have -> : closure [set` Interval -oo%O (BSide y b)] = `]-oo, b]%classic.
    case: y.
      rewrite set_itv_infty_o set_itv_infty_c.
      by rewrite closure_lt.
    apply/esym.
    apply/closure_id.
    rewrite set_itv_infty_c.
    exact: closed_le.
  move=> H.
  by rewrite set_itv_splitI.
have -> : `[a, b]%classic = closure `]a, b[%classic.
  rewrite eqEsubset; split.
    move=> r /=.
    rewrite in_itv/=.
    move/andP => [].
    rewrite le_eqVlt; move/predU1P => [-> |ar].
      
      admit.
    admit.
  admit.
apply: closure_subset.
move=> r /=.
rewrite in_itv/=.
move/andP => [ar rb].
rewrite in_itv.
by case: x => /=; rewrite ?ltW ?ar //=; case: y => /=; rewrite ?ltW ?rb /=.
Admitted.

Lemma subset_neitv_oocc a b c d : a < b ->
  `]a, b[ `<=` `[c, d] ->
  `[a, b] `<=` `[c, d].
Proof.
move=> ab.
move/closure_subset.
rewrite -(closure_id `[c, d]%classic).1; last first.
  admit.
apply: subset_trans.
Admitted.

Lemma get_nice_image_itv f a b (n : nat) (ab_ : nat -> R * R) : a < b ->
  {within `[a, b], continuous f} ->
  {in `]a, b[ &, nondecreasing_fun f} ->
  (forall i, (i < n)%N -> (ab_ i).1 < (ab_ i).2) ->
  (forall i, (i < n)%N -> `](ab_ i).1, (ab_ i).2[ `<=` `[a, b]) ->
  trivIset (`I_ n) (fun i=> `](ab_ i).1, (ab_ i).2[%classic) ->
exists (m : nat) (fab_ : nat -> R * R),
  [/\ (forall i, (i < m)%N -> `](fab_ i).1, (fab_ i).2[ `<=` f @` `[a, b]),
     (forall i, (i < m)%N -> (fab_ i).1 < (fab_ i).2),
      trivIset (`I_ m) (fun i => `](fab_ i).1, (fab_ i).2[%classic),
      \big[setU/set0]_(i < n) (f @` `](ab_ i).1, (ab_ i).2[%classic) =
      \big[setU/set0]_(i < m) `](fab_ i).1, (fab_ i).2[%classic &
      mu (\big[setU/set0]_(i < m) `](fab_ i).1, (fab_ i).2[%classic) =
      (\sum_(i < n) (f (ab_ i).2 - f (ab_ i).1))%:E ].
Proof.
move=> ab cf ndf ablt absub tab.
(* have ndfcc := continuous_in_nondecreasing_oo_cc ab cf ndf. *)
have [cf' [fxa fxb]] := (continuous_within_itvP f ab).1 cf.
have cfab i : (i < n)%N -> {within `[(ab_ i).1, (ab_ i).2], continuous f}.
  move=> iltn.
  move: cf.
  apply: continuous_subspaceW.
  apply: subset_neitv_oocc.
    exact: (ablt i).
  exact: (absub i).
have ndfab i :(i < n)%N -> {in `](ab_ i).1, (ab_ i).2[ &, {homo f: n m / n <= m}}.
  admit.
have fab0 i (Hi : (i < n)%N) := continuous_nondecreasing_image_itvoo_itv (ablt i Hi) (cfab i Hi) (ndfab i Hi).
exists n.
exists (fun n => (f (ab_ n).1, f (ab_ n).2)).
split.
        move=> i iltn /=.
        move=> x/=.
        rewrite in_itv/=.
        move=> /andP[fabix xfabi].
        have /(IVT (ltW (ablt i iltn)) (cfab i iltn)) : minr (f (ab_ i).1) (f (ab_ i).2) <= x <= maxr (f (ab_ i).1) (f (ab_ i).2).
        rewrite ge_min le_max.
        apply/andP; split.
        - by apply/orP; left; rewrite ltW.
        - by apply/orP; right; rewrite ltW.
        move=> [r + frx].
        rewrite -frx.
        rewrite in_itv/=.
        move/andP => [].
        rewrite le_eqVlt.
        move/predU1P => [<- _|abir].
          exists (ab_ i).1 => //.
          admit.
        rewrite le_eqVlt.
        move/predU1P => [-> |rabi].
          exists (ab_ i).2 => //.
          admit.
        exists r => //.
        rewrite in_itv/=.
        apply/andP; split.
          apply: le_trans (ltW abir).
          admit.
        apply: (le_trans (ltW rabi)).
        admit.
      rewrite /=.
      admit.
    admit.
  admit.
admit.
Admitted.

End image_of_itv.

Section PRme.
Context {R : realType}.

Lemma near_eq_lim (*(R : realFieldType)*) (f g : nat -> \bar R) :
  cvgn g -> {near \oo, f =1 g} -> limn f = limn g.
Admitted.

Lemma lim_shift_cst (*(R : realFieldType)*) (u : (\bar R) ^nat) (l : \bar R) :
    cvgn u -> (forall n, 0 <= u n)%E -> (-oo < l)%E ->
  limn (fun x => l + u x) = l + limn u.
Admitted.

Local Open Scope ereal_scope.
Lemma nneseriesD1 (f : nat -> \bar R) n :
  (forall k, 0 <= f k) ->
  \sum_(0 <= k <oo) f k = f n + \sum_(0 <= k <oo | k != n) f k.
Proof.
move=> f0.
rewrite -lim_shift_cst//.
- apply: (@near_eq_lim _ (fun x => f n + _)).
  + apply: is_cvgeD => //.
    * rewrite ge0_adde_def// inE.
        by rewrite lim_cst.
      exact: nneseries_ge0.
    * exact: is_cvg_cst.
    * exact: is_cvg_ereal_nneg_natsum_cond.
  + near=> k.
    have nk : (n < k)%N.
      near: k.
      exact: nbhs_infty_gt.
    rewrite big_mkord.
    rewrite (bigD1 (Ordinal nk))//=.
    by rewrite big_mkord.
- exact: is_cvg_ereal_nneg_natsum_cond.
- by move=> m; exact: sume_ge0.
- by rewrite (@lt_le_trans _ _ 0).
Unshelve. all: by end_near. Qed.

End PRme.

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

Section completed_measure_extension.
Local Open Scope ereal_scope.
Context d (T : semiRingOfSetsType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Notation rT := (SetRing.type T).
Let Rmu : set rT -> \bar R := SetRing.measure mu.

Let I := [the measurableType _ of caratheodory_type (mu^*)%mu].

Definition completed_measure_extension : set I -> \bar R := (mu^*)%mu.

Let measure0 : completed_measure_extension set0 = 0.
Proof. exact: mu_ext0. Qed.

Let measure_ge0 (A : set I) : 0 <= completed_measure_extension A.
Proof. exact: mu_ext_ge0. Qed.

Let measure_semi_sigma_additive :
  semi_sigma_additive completed_measure_extension.
Proof.
move=> F mF tF mUF; rewrite /completed_measure_extension.
exact: caratheodory_measure_sigma_additive.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ completed_measure_extension
  measure0 measure_ge0 measure_semi_sigma_additive.

Lemma completed_measure_extension_sigma_finite : @sigma_finite _ T _ setT mu ->
  @sigma_finite _ _ _ setT completed_measure_extension.
Proof.
move=> -[S setTS mS]; exists S => //; move=> i; split.
- apply: sub_caratheodory; apply: sub_sigma_algebra.
  exact: (mS i).1.
- by rewrite /completed_measure_extension /= measurable_mu_extE //;
    [exact: (mS i).2 | exact: (mS i).1].
Qed.

End completed_measure_extension.


Section completed_lebesgue_stieltjes_measure.
Context {R : realType}.

Definition completed_lebesgue_stieltjes_measure (f : cumulative R) :=
  @completed_measure_extension _ _ _ [the measure _ _ of wlength f].

HB.instance Definition _ (f : cumulative R) :=
  Measure.on (@completed_lebesgue_stieltjes_measure f).

Let sigmaT_finite_completed_lebesgue_stieltjes_measure (f : cumulative R) :
  sigma_finite setT (@completed_lebesgue_stieltjes_measure f).
Proof. exact/completed_measure_extension_sigma_finite/wlength_sigma_finite. Qed.

HB.instance Definition _ (f : cumulative R) :=
  @Measure_isSigmaFinite.Build _ _ _
    (@completed_lebesgue_stieltjes_measure f)
    (sigmaT_finite_completed_lebesgue_stieltjes_measure f).

End completed_lebesgue_stieltjes_measure.
Arguments completed_lebesgue_stieltjes_measure {R}.


Definition completed_lebesgue_measure {R : realType} : set _ -> \bar R :=
  [the measure _ _ of
    completed_lebesgue_stieltjes_measure [the cumulative _ of idfun]].
HB.instance Definition _ (R : realType) :=
  Measure.on (@completed_lebesgue_measure R).
HB.instance Definition _ (R : realType) :=
  SigmaFiniteMeasure.on (@completed_lebesgue_measure R).

Lemma completed_lebesgue_measureE {R : realType} :
  (@completed_lebesgue_measure R) = (@lebesgue_measure R).
Proof. by []. Qed.

Lemma sigma_algebra_mu_ext {R : realType} :
  sigma_algebra [set: ocitv_type R] (wlength idfun)^*%mu.-cara.-measurable.
Proof.
split.
- exact: caratheodory_measurable_set0.
- by move=> A mA; rewrite setTD; exact: caratheodory_measurable_setC.
- by move=> F mF; exact: caratheodory_measurable_bigcup.
Qed.

Lemma completed_lebesgue_measure_is_complete {R : realType} :
  measure_is_complete (@completed_lebesgue_measure R).
Proof. exact: measure_is_complete_caratheodory. Qed.


Definition completed_algebra_gen d {T : semiRingOfSetsType d} {R : realType}
    (mu : set T -> \bar R) : set _ :=
  [set A `|` N | A in d.-measurable & N in mu.-negligible].

(*Definition completed_algebra d {T : semiRingOfSetsType d} {R : realType}
    (mu : set T -> \bar R) : measurableType _ :=
  salgebraType (completed_algebra_gen mu).*)

Lemma setDU {T} (U V W : set T) : U `<=` V -> V `<=` W ->
  W `\` U = (W `\` V) `|` (V `\` U).
Proof.
move=> UV VW; apply/seteqP; split.
  move=> x [Wx Ux].
  by have [Vx|Vx] := pselect (V x); [right|left].
move=> x [[Wx Vx]|[Vx Ux]].
- by split => // /UV.
- by split => //; exact/VW.
Qed.

(* the completed sigma-algebra is the same as the caratheodory sigma-algebra *)
Section completed_algebra_cara.
Context {R : realType}.

Let cara_sub_calgebra : ((wlength idfun)^*)%mu.-cara.-measurable `<=`
  (completed_algebra_gen (@lebesgue_measure R)).-sigma.-measurable.
Proof.
move=> E.
wlog : E / (completed_lebesgue_measure E < +oo)%E.
  move=> /= wlg.
  have /sigma_finiteP[/= F [UFI ndF mF]] :=
    measure_extension_sigma_finite (@wlength_sigma_finite R idfun).
  move=> mE.
  rewrite -(setIT E)/= UFI setI_bigcupr; apply: bigcupT_measurable => i.
  apply: wlg.
  - rewrite (le_lt_trans _ (mF i).2)//= le_measure// inE/=.
    + by apply: measurableI => //; apply: sub_caratheodory; exact: (mF i).1.
    + by apply: sub_caratheodory; exact: (mF i).1.
  - by apply: measurableI => //; apply: sub_caratheodory; exact: (mF i).1.
move=> mEoo mE.
have inv0 n : 0 < n.+1%:R^-1 :> R by rewrite invr_gt0.
set S :=
  [set (\sum_(0 <= k <oo) wlength idfun (A k))%E | A in measurable_cover E].
have H1 s : 0 < s ->
     exists2 A_ : (set R) ^nat,
       @measurable_cover _ (ocitv_type R) E A_ &
       (\sum_(0 <= k <oo) wlength idfun (A_ k) <
        completed_lebesgue_measure E + s%:E)%E.
  move=> s0.
  have : lebesgue_measure E \is a fin_num by rewrite ge0_fin_numE.
  move/lb_ereal_inf_adherent => /(_ _ s0)[_/= [A_ EA_] <-] ?.
  by exists A_.
pose A_ n := projT1 (cid2 (H1 _ (inv0 n))).
have mA k : @measurable_cover _ (ocitv_type R) E (A_ k).
  by rewrite /A_; case: cid2.
have mA_E n : (\sum_(0 <= k <oo) wlength idfun (A_ n k) <
    completed_lebesgue_measure E + n.+1%:R^-1%:E)%E.
  by rewrite /A_; case: cid2.
pose F_ n := \bigcup_m (A_ n m).
have EF_n n : E `<=` F_ n.
  have [/= _] := mA n.
  move=> /subset_trans; apply.
  by apply: subset_bigcup => i _.
have mF_ m : (lebesgue_measure (F_ m) <
    completed_lebesgue_measure E + m.+1%:R^-1%:E)%E.
  apply: (le_lt_trans _ (mA_E m)).
  rewrite /lebesgue_measure/= /lebesgue_stieltjes_measure/= /measure_extension/=.
  apply: (le_trans
   (outer_measure_sigma_subadditive (@wlength R idfun)^*%mu (A_ m))).
  apply: lee_nneseries => // n _.
  rewrite -((measurable_mu_extE (@wlength R idfun)) (A_ m n))//.
  by have [/(_ n)] := mA m.
pose F := \bigcap_n (F_ n).
have FM : @measurable _ (salgebraType R.-ocitv.-measurable) F.
  apply: bigcapT_measurable => k; apply: bigcupT_measurable => i.
  by apply: sub_sigma_algebra; have [/(_ i)] := mA k.
have EF : E `<=` F by exact: sub_bigcap.
have muEF : completed_lebesgue_measure E = lebesgue_measure F.
  apply/eqP; rewrite eq_le; apply/andP; split.
    by rewrite le_outer_measure.
  apply/lee_addgt0Pr => /= _/posnumP[e].
  near \oo => n.
  apply: (@le_trans _ _ (lebesgue_measure (F_ n))).
    by apply: le_outer_measure; exact: bigcap_inf.
  apply: (le_trans (ltW (mF_ n))).
  rewrite leeD// lee_fin ltW//.
  by near: n; apply: near_infty_natSinv_lt.
have H2 (s : R) : 0 < s ->
     exists2 A_ : (set R) ^nat,
       @measurable_cover _ (ocitv_type R) (F `\` E) A_ &
       (\sum_(0 <= k <oo) wlength idfun (A_ k) <
        completed_lebesgue_measure (F `\` E) + s%:E)%E.
  move=> s0.
  have : lebesgue_measure (F `\` E) \is a fin_num.
    rewrite ge0_fin_numE// (@le_lt_trans _ _ (lebesgue_measure F))//.
      by apply: le_outer_measure; exact: subDsetl.
    by rewrite -muEF.
  move/lb_ereal_inf_adherent => /(_ _ s0)[_/= [B_ FEB_] <-] ?.
  by exists B_.
pose B_ n := projT1 (cid2 (H2 _ (inv0 n))).
have mB k : @measurable_cover _ (ocitv_type R) (F `\` E) (B_ k).
  by rewrite /B_; case: cid2.
have mB_FE n : (\sum_(0 <= k <oo) wlength idfun (B_ n k) <
        completed_lebesgue_measure (F `\` E) + n.+1%:R^-1%:E)%E.
  by rewrite /B_; case: cid2.
pose G_ n := \bigcup_m (B_ n m).
have FEG_n n : F `\` E `<=` G_ n.
  have [/= _] := mB n.
  move=> /subset_trans; apply.
  by apply: subset_bigcup => i _.
have mG_ m : (lebesgue_measure (G_ m) <
             completed_lebesgue_measure (F `\` E) + m.+1%:R^-1%:E)%E.
  apply: (le_lt_trans _ (mB_FE m)).
  rewrite /lebesgue_measure/= /lebesgue_stieltjes_measure/= /measure_extension/=.
  apply: (le_trans (outer_measure_sigma_subadditive (@wlength R idfun)^*%mu (B_ m))).
  apply: lee_nneseries => // n _.
  have <-// := (measurable_mu_extE (@wlength R idfun)) (B_ m n).
  by have [/(_ n)] := mB m.
pose G := \bigcap_n (G_ n).
have GM : @measurable _ (salgebraType R.-ocitv.-measurable) G.
  apply: bigcapT_measurable => k; apply: bigcupT_measurable => i.
  by apply: sub_sigma_algebra; have [/(_ i)] := mB k.
have FEG : F `\` E `<=` G by exact: sub_bigcap.
have muG : lebesgue_measure G = 0.
  transitivity (completed_lebesgue_measure (F `\` E)).
    apply/eqP; rewrite eq_le; apply/andP; split; last exact: le_outer_measure.
    apply/lee_addgt0Pr => _/posnumP[e].
    near \oo => n.
    apply: (@le_trans _ _ (lebesgue_measure (G_ n))).
      by apply: le_outer_measure; exact: bigcap_inf.
    apply/ltW/(lt_le_trans (mG_ n)).
    rewrite leeD// lee_fin ltW//.
    by near: n; apply: near_infty_natSinv_lt.
  rewrite measureD//=.
  + rewrite setIidr// muEF subee// ge0_fin_numE//.
    by move: mEoo; rewrite muEF.
  + exact: sub_caratheodory.
  + by move: mEoo; rewrite muEF.
apply: sub_sigma_algebra; exists (F `\` G); first exact: measurableD.
exists (E `&` G).
  apply: (@negligibleS _ _ _ lebesgue_measure G).
    exact: subIsetr.
  by exists G; split.
apply/seteqP; split=> [/= x [[Fx Gx]|[]//]|x Ex].
- rewrite -(notK (E x)) => Ex.
  by apply: Gx; exact: FEG.
- have [|FGx] := pselect ((F `\` G) x); first by left.
  right; split => //.
  move/not_andP : FGx => [|].
    by have := EF _ Ex.
  by rewrite notK.
Unshelve. all: by end_near. Qed.

Lemma completed_salgebra_lebesgue_measure :
  (completed_algebra_gen (@lebesgue_measure R)).-sigma.-measurable =
  @completed_algebra_gen _ _ R (@lebesgue_measure R).
Proof.
apply/seteqP; split; last first.
  move=> X [/= A /= mA [N neglN]] <-{X}.
  apply: sub_sigma_algebra.
  by exists A => //; exists N.
apply: smallest_sub => //=; split => /=.
- exists set0 => //; exists set0 => //; first exact: negligible_set0.
  by rewrite setU0.
- move=> G [/= A mA [N negN ANG]].
  case: negN => /= F [mF F0 NF].
  have H1 : ~` G = ~` A `\` (N `&` ~` A).
    by rewrite -ANG setCU setDE setCI setCK setIUr setICl setU0.
  pose AA := ~` A `\` (F `&` ~` A).
  pose NN := (F `&` ~` A) `\` (N `&` ~` A).
  have H2 : ~` G = AA `|` NN.
    rewrite (_ : ~` G = ~` A `\` (N `&` ~` A))//.
    by apply: setDU; [exact: setSI|exact: subIsetr].
  exists AA.
    apply: measurableI => //=; first exact: measurableC.
    by apply: measurableC; apply: measurableI => //; exact: measurableC.
  exists NN.
    by exists F; split => // x [] [].
  by rewrite setDE setTI.
- move=> F mF/=.
  rewrite /completed_algebra_gen/=.
  pose A n := projT1 (cid2 (mF n)).
  pose N n := projT1 (cid2 (projT2 (cid2 (mF n))).2).
  exists (\bigcup_k A k).
    apply: bigcupT_measurable => i.
    by rewrite /A; case: cid2 => //.
  exists (\bigcup_k N k).
    apply: negligible_bigcup => /= k.
    rewrite /N; case: (cid2 (mF k)) => //= *.
    by case: cid2 => //.
  rewrite -bigcupU.
  apply: eq_bigcup => // i _.
  rewrite /A /N; case: (cid2 (mF i)) => //= *.
  by case: cid2 => //=.
Qed.

Lemma negligible_sub_caratheodory :
  (@completed_lebesgue_measure R).-negligible `<=`
  ((wlength idfun)^*)%mu.-cara.-measurable.
Proof.
move=> N /= [/= A] [mA A0 NA].
have H1 : ((wlength idfun)^*)%mu N = 0.
  apply/eqP; rewrite eq_le; apply/andP; split.
    rewrite -A0.
    rewrite (_ : completed_lebesgue_measure A = ((wlength idfun)^*)%mu A)//.
    by apply: le_outer_measure.
  exact: outer_measure_ge0.
apply: le_caratheodory_measurable => /= X.
apply: (@le_trans _ _ (((wlength idfun)^*)%mu (N) +
   ((wlength idfun)^*)%mu (X `&` ~` N))).
  rewrite leeD2r//.
  apply: le_outer_measure.
  exact: subIsetr.
rewrite H1 add0e.
apply: le_outer_measure.
exact: subIsetl.
Qed.

Let calgebra_sub_cara :
  (completed_algebra_gen (@lebesgue_measure R)).-sigma.-measurable `<=`
  ((wlength idfun)^*)%mu.-cara.-measurable.
Proof.
rewrite completed_salgebra_lebesgue_measure => A -[/= X mX] [N negN] <-{A}.
apply: measurableU => //; first exact: sub_caratheodory.
apply: negligible_sub_caratheodory.
case: negN => /= B [mB B0 NB].
by exists B; split => //=; exact: sub_caratheodory.
Qed.

Lemma completed_caratheodory_measurable :
  (completed_algebra_gen (@lebesgue_measure R)).-sigma.-measurable =
  (wlength idfun)^*%mu.-cara.-measurable.
Proof.
by apply/seteqP; split => /=;
  [exact: calgebra_sub_cara|exact: cara_sub_calgebra].
Qed.

End completed_algebra_cara.

(*mu^*(A)=0 -> A satisfies caratheodory criterion

https://math.stackexchange.com/questions/2913728/complete-measures-and-complete-sigma-algebras*)

Definition open_itv_cover {R : realType} (X : set R) :=
  [set F : (set R)^nat |
    (forall i, (is_interval (F i) /\ open (F i))) /\ X `<=` \bigcup_k (F k)].

Definition ocitv_cover {R : realType} (X : set R) :=
  [set F : (set R)^nat |
    (forall i, (ocitv (F i))) /\ X `<=` \bigcup_k (F k)].

Section li.

Lemma pro20 {R : realType} (X : set R) :
  ((wlength idfun)^*)%mu X =
  ereal_inf [set \sum_(k <oo) wlength idfun (A k) | A in open_itv_cover X]%E.
Proof.
case Xoo : (((wlength idfun)^*)%mu X == +oo%E).

apply/eqP; rewrite eq_le; apply/andP; split.
  apply: le_ereal_inf => x/= [I_ [mI_ XI_ <-{x}]].
  move: mI_.
  move/all_and2 => [itvI oI].
  have : forall k, exists (ab_ : nat -> R * R), I_ k = `](ab_ k).1, (ab_ k).2]%classic.
    move=> k.
    move: (itvI k).
    rewrite is_intervalP.
    rewrite /Rhull.

    move ->.
    
  admit.
Admitted.

Definition cmu {R : realType} := (@(*completed_*)lebesgue_measure R).

Lemma pro211 {R : realType} (X : set R) :
  (((wlength idfun)^*)%mu X < +oo)%E ->
  forall e, 0 < e -> exists U, [/\ open U,
    X `<=` U &
    (cmu U <= ((wlength idfun)^*)%mu X + e%:E)%E].
Proof.
move=> Xoo/= e e0.
have := pro20 X.
set ei := (X in _ = X -> _) => Xei.
have : ei \is a fin_num.
  rewrite ge0_fin_numE//; first by rewrite -Xei.
  apply: lb_ereal_inf => _ [F _ <-].
  by apply: nneseries_ge0 => n _; exact: wlength_ge0.
move=> /lb_ereal_inf_adherent => /(_ _ e0)[_ /= [I_ HI_]] <-.
rewrite -/ei -Xei {Xei ei} => I_X.
exists (\bigcup_i (I_ i)); split.
- by apply: bigcup_open => i _; have [] := HI_.1 i.
- exact: HI_.2.
- rewrite (le_trans _ (ltW I_X))//.
  case: HI_ => HI_1 HI_2.
  apply: (@le_trans _ _ (\big[+%R/0%R]_(0 <= k <oo) cmu (I_ k))%E).
    exact: outer_measure_sigma_subadditive.
  apply: lee_nneseries => // n _.
  have I_E : exists a b, I_ n = `]a, b[%classic.
    admit.
  have [a [b ->]] := I_E.
  apply: (@le_trans _ _ (cmu `]a, b])).
    apply: le_outer_measure.
    by apply/subset_itv_oo_oc.
  rewrite /cmu/=.
  rewrite /lebesgue_measure/=.
  rewrite /lebesgue_stieltjes_measure/=.
  rewrite /measure_extension/=.
  rewrite /completed_lebesgue_measure/=.
  rewrite /completed_lebesgue_stieltjes_measure/=.
  rewrite /completed_measure_extension/=.
  rewrite measurable_mu_extE//=; last first.
    by exists (a, b) => //.
  by rewrite !wlength_itv.
Admitted.

Lemma pro212 {R : realType} (X : set R) :
  (((wlength idfun)^*)%mu X < +oo)%E ->
  exists G_ : (set R)^nat, [/\ (forall i, open (G_ i)),
    X `<=` \bigcap_i G_ i &
    cmu (\bigcap_i G_ i) = ((wlength idfun)^*)%mu X].
Proof.
move=> Xoo.
have inv0 (k : nat) : (0 < k.+1%:R^-1 :> R) by rewrite invr_gt0.
pose U_ (k : nat) := projT1 (cid (pro211 Xoo (inv0 k))).
have oU_ (k : nat) : open (U_ k) by rewrite /U_; case: cid => x /= [].
have XU_ (k : nat) : X `<=` U_ k by rewrite /U_; case: cid => x /= [].
have mUX (k : nat) :
  (cmu (U_ k) <=
   ((wlength idfun)^*)%mu X + k.+1%:R^-1%:E)%E.
  by rewrite /U_; case: cid => x /= [].
pose G := \bigcap_k (U_ k).
exists U_; split => //; first by apply: sub_bigcap.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply/lee_addgt0Pr => /= _/posnumP[e].
  near \oo => k.
  apply: (@le_trans _ _ (((wlength idfun)^*)%mu X + k.+1%:R^-1%:E)).
    apply: (le_trans _ (mUX k)).
    apply: le_outer_measure.
    by apply: bigcap_inf.
  rewrite leeD2l// lee_fin; apply: ltW.
  by near: k; exact: near_infty_natSinv_lt.
rewrite [leRHS](_ : _ = ((wlength idfun)^*)%mu (\bigcap_i U_ i))//.
apply: le_outer_measure.
exact: sub_bigcap.
Unshelve. all: by end_near. Qed.

Lemma cor22 {R : realType} (N : set R) :
  (@cmu R).-negligible N <->
  ((wlength idfun)^*)%mu N = 0.
Proof.
split.
  move=> [/= A [mA cmuA NA]].
  apply/eqP; rewrite eq_le outer_measure_ge0 andbT.
  rewrite (@le_trans _ _ (((wlength idfun)^*)%mu A))//.
    exact: le_outer_measure.
  move: cmuA.
  rewrite /cmu/=.
  rewrite /lebesgue_measure/=.
  rewrite /lebesgue_stieltjes_measure.
  rewrite /measure_extension/=.
  rewrite /completed_lebesgue_measure/=.
  rewrite /completed_lebesgue_stieltjes_measure.
  by rewrite /completed_measure_extension/= => ->.
move=> N0.
have := @pro212 _ N.
rewrite N0 ltry => /(_ isT)[G_ [oG_ NG_ mG_0]].
exists (\bigcap_i G_ i); split => //=.
apply: bigcapT_measurable => i.
apply: open_measurable => //=.
(*split.
  exact: sigma_algebra_mu_ext.
by move=> A mA; apply: sub_caratheodory; exact: sub_sigma_algebra.*)
Qed.

End li.

(* TODO: move to topology.v *)
Section Gdelta.
Context (R : realType).

Definition Gdelta (S : set R) :=
  exists2 A_ : (set R)^nat, (forall i, open (A_ i)) & S = \bigcap_i (A_ i).

Lemma open_Gdelta (S : set R) : open S -> Gdelta S.
Proof.
exists (bigcap2 S setT) => [i|]; last by rewrite bigcap2E setIT.
by rewrite /bigcap2; case: ifP => // _; case: ifP => // _; exact: openT.
Qed.

Lemma Gdelta_measurable (S : set R) : Gdelta S -> (@measurable _ R) S.
Proof.
by move=> [] B oB ->; apply: bigcapT_measurable => i; exact: open_measurable.
Qed.

End Gdelta.

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
rewrite /= !in_itv/= midf_lt//=; last by rewrite lt_minr Bi1a B12.
have : ((B i).1 + minr a (B i).2)%E / 2 < (B i).2.
  by rewrite ltr_pdivrMr// mulr_natr mulr2n ltr_leD// le_minl lexx orbT.
move=> /[swap] /[apply] /andP[+ _].
rewrite ler_pdivlMr// mulr_natr mulr2n leNgt => /negP; apply.
by rewrite ltr_leD// le_minl lexx.
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
rewrite /= !in_itv/= midf_lt//=; last by rewrite lt_maxl Bi2b B12.
rewrite andbT.
have : (B i).1 < (maxr (B i).1 b + (B i).2)%E / 2.
  by rewrite ltr_pdivlMr// mulr_natr mulr2n ler_ltD// le_maxr lexx.
move=> /[swap] /[apply] /andP[_].
rewrite ler_pdivrMr// mulr_natr mulr2n leNgt => /negP; apply.
by rewrite ler_ltD// le_maxr lexx orbT.
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

Section absolute_continuity.
Context {R : realType}.

Definition abs_cont (a b : R) (f : R -> R) := forall e : {posnum R},
  exists d : {posnum R}, forall n (B : nat -> R * R), (* B : 'I_n -> R * R *)
    [/\ (forall i, (i < n)%N -> ((B i).1 < (B i).2 /\ `](B i).1, (B i).2[ `<=` `[a, b])),
        trivIset `I_n (fun i => `](B i).1, (B i).2[%classic) &
        \sum_(k < n) ((B k).2 - (B k).1) < d%:num] ->
    \sum_(k < n) (f (B k).2 - f ((B k).1)) < e%:num.

(* lemma8 *)
Lemma total_variation_AC a b (f : R -> R) : a < b ->
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
rewrite (total_variationD f aBi1 (ltW B12)) fineD; last 2 first.
  apply/(bounded_variationP f aBi1)/(@bounded_variationl _ _ _ b) => //.
  by rewrite (le_trans _ Bi2b)// ltW.
  apply/(bounded_variationP f (ltW B12)).
  apply/(bounded_variationl (ltW B12) Bi2b).
  by apply: (bounded_variationr aBi1) => //; rewrite (le_trans _ Bi2b)// ltW.
rewrite addrAC subrr add0r -subr_ge0 -lee_fin EFinB fineK; last first.
  apply/(bounded_variationP f (ltW B12)).
  apply/(bounded_variationl (ltW B12) Bi2b).
  by apply/(bounded_variationr aBi1 _ BVf); rewrite (le_trans _ Bi2b)// ltW.
by rewrite leeBrDr// add0e total_variation_ge// ltW.
Qed.

End absolute_continuity.

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
Proof. by rewrite -set_itv_infty_infty lebesgue_measure_itv. Qed.

Lemma completed_lebesgue_measure_itv {R : realType} (i : interval R) :
  completed_lebesgue_measure ([set` i] : set R) =
  (if i.1 < i.2 then (i.2 : \bar R) - i.1 else 0)%E.
Proof.
Admitted.

Lemma completed_lebesgue_measureT {R : realType} :
  (@completed_lebesgue_measure R) setT = +oo%E.
Proof.
by rewrite -set_itv_infty_infty completed_lebesgue_measure_itv.
Qed.

Lemma wlength_idfun_le {R : realType} : forall A, R.-ocitv.-measurable A ->
  ((@wlength R idfun) A <= ((wlength idfun)^*)%mu A)%E.
Proof.
move=> A mA; apply: lb_ereal_inf => /= _ [F [mF AF] <-].
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
have [->|] := eqVneq (mu E) +oo%E.
  exists setT; split => //; first exact: openT.
  by rewrite leey andbT -set_itv_infty_infty lebesgue_measure_itv.
rewrite -ltey -ge0_fin_numE; last exact: outer_measure_ge0.
move=> /[dup] mEfin => /lb_ereal_inf_adherent.
set infE := ereal_inf _.
have e20 : 0 < e / 2 by rewrite divr_gt0.
move=> /(_ _ e20)[x [/= Q EQ <- muEoo]].
have [/= T QT TQ] : exists2 T : nat -> set R,
    (forall k, Q k `<=` interior (T k)) &
    (forall k, mu (T k) <= mu (Q k) + (e / (2 ^+ k.+2))%:E)%E.
  have mQfin k : mu (Q k) \is a fin_num.
    rewrite ge0_fin_numE//.
    apply: (@le_lt_trans _ _ (\sum_(0 <= k <oo) wlength idfun (Q k)))%E.
      rewrite /mu/= /lebesgue_stieltjes_measure/= /measure_extension/=.
      rewrite measurable_mu_extE /=; last by move: EQ => [+ _]; exact.
      by rewrite (nneseriesD1 k) // leeDl// nneseries_ge0.
    by rewrite (lt_le_trans muEoo)// leey.
  have /choice[T /= TH] : forall k, exists T : set R,
      [/\ open T, (Q k) `<=` T & (mu (T `\` Q k) < (e / 2 ^+ k.+2)%:E)%E].
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

(* Theorem 1.17 https://heil.math.gatech.edu/6337/spring11/section1.1.pdf *)
(* was outer_regularity_outer *)
Lemma lebesgue_regularity_outer_inf (E : set R) :
  mu E = ereal_inf [set mu U | U in [set U | open U /\ E `<=` U]].
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: lb_ereal_inf => /= r /= [A [oA EA] <-{r}].
  apply: le_ereal_inf => _ /= [] S_ AS_ <-; exists S_ => //.
  move: AS_ => [mS_ AS_].
  by split; [exact: mS_|exact: (subset_trans EA)].
- apply/lee_addgt0Pr => /= e e0.
  have [U [oU EU /andP[UE UEe]]] := outer_regularity_outer0 E e0.
  apply: ereal_inf_le => /=.
  exists (mu U) => //.
  by exists U.
Qed.

End lebesgue_regularity_outer_inf.

Section lebesgue_measurable.
Context {R : realType}.

Let mue := ((@wlength R idfun)^*)%mu.

Definition lebesgue_measurability (E : set R) :=
  forall eps : R, 0 < eps -> exists U, [/\ open U,
  E `<=` U & (mue (U `\` E) <= eps%:E)%E].

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
    apply: bigcap_measurable => ? ?.
    by apply: open_measurable.
  rewrite SB.
  apply: bigcap_measurable => ? ?.
  by apply: open_measurable.
  rewrite (@le_lt_trans _ _ (mue (U_ 0%N)))//.
  apply: le_outer_measure.
  apply: bigcap_inf.
  near: k.
  by exists 1%N.
  have [/andP[_]] := leU_ 0%N.
  move=> /le_lt_trans; apply.
  rewrite -exprVn expr0.
  by rewrite lte_add_pinfty// ltry.
- rewrite /Uoo_trunc.
  rewrite lee_subel_addl//.
  rewrite setIidr//; last first.
    by apply: sub_bigcap.
  rewrite (@le_trans _ _ (mue (U_ k)))//.
    apply: le_outer_measure.
      by apply: bigcap_inf => /=.
  have [/andP[_]] := leU_ k.
  move=> /le_trans; apply.
  rewrite leeD2l//.
  rewrite lee_fin.
  rewrite -div1r.
  apply/ltW.
  near: k.
  exact: near_infty_natSinv_expn_lt.
Unshelve. all: by end_near. Qed.

(* Theorem 1.36 in https://heil.math.gatech.edu/6337/spring11/section1.3.pdf *)
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
  ((wlength idfun)^*)%mu A = 0 -> lebesgue_measurability A.
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
rewrite A0 add0e => /andP[mU0 mUe].
exists U; split => //.
rewrite (le_trans _ mUe)//.
apply: le_outer_measure.
exact: subDsetl.
Qed.

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

Lemma abs_contN_dominates a b (f : cumulative R) : abs_contN a b f ->
  mu `<< lebesgue_stieltjes_measure f.
Abort.

Fail Lemma differentiable_lusinN a b f : {in `]a, b[%classic, differentiable f} ->
  lusinN `]a, b[%classic f.

End lusinN.

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

Section lemma1.
Context {R : realType}.

Definition not_subset01 (X : set R) (Y : set R) (f : {fun X >-> Y}) : set R :=
  Y `&` [set y | (X `&` f @^-1` [set y] !=set0) /\
         ~ is_subset1 (X `&` f @^-1` [set y])].

(* Lemma not_subset01P (X : set R) (Y : set R) (f : {fun X >-> Y}) : *)
(*   not_subset01 f -> *)
(*   (exists x0 x1, *)
(*    [/\ x0 \in (Y `&` [set y | (X `&` f @^-1` [set y])]), *)
(*       x1 \in (Y `&` [set y | (X `&` f @^-1` [set y])]) & *)
(*       x0 != x1]). *)

Lemma lemma1 (X : set R) (Y : set R) (f : {fun X >-> Y}) (I : pointedType)
    (X_ : I -> set R) :
    (forall i, X_ i `<=` X) ->
  (\bigcap_i (f @` X_ i)) `\` not_subset01 f `<=` f @` (\bigcap_i X_ i) /\
  f @` (\bigcap_i X_ i) `<=` \bigcap_i (f @` X_ i).
Proof.
move=> X_x; split; last first.
  (* TODO: lemma? *)
  move=> _/= [x fX_x] <- i _; exists x => //.
  exact: fX_x.
move=> y [bigcap_y fy01].
have Yy : Y y.
  have [x X_pointx <-] := bigcap_y point Logic.I.
  by apply/funS/X_x; exact: X_pointx.
have [x [Xx yfx x_unique]] :
    exists x, [/\ X x, y = f x & forall x', X x' -> y = f x' -> x' = x].
  move/not_andP : fy01 => [//|/not_andP[|]].
  - move=> /set0P/negP/negPn/eqP fy0.
    have [x X_pointx fxy] := bigcap_y point Logic.I.
    exfalso.
    move: fy0 => /eqP/negPn/negP; apply.
    apply/set0P; exists x; split => //.
    apply: X_x.
    exact: X_pointx.
  - move=> /contrapT y_unique.
    have [|] := pselect (X `&` f @^-1` [set y] !=set0); last first.
      (* TODO: redundant with the previous subgoal *)
      move=> /set0P/negP/negPn/eqP fy0.
      have [x X_pointx fxy] := bigcap_y point Logic.I.
      exfalso.
      move: fy0 => /eqP/negPn/negP; apply.
      apply/set0P; exists x; split => //.
      apply: X_x.
      exact: X_pointx.
    move=> [x0 [Xx0 fyx0]].
    exists x0; split => // x' Xx' yfx'.
    exact: y_unique.
have X_f i : exists xi, X_ i xi /\ f xi = y.
  have [xi X_ixi <-] : (f @` X_ i) y by exact: bigcap_y.
  by exists xi.
exists x => // i _.
have [xi [X_ixi fxiy]] := X_f i.
have Xxi : X xi by apply: X_x; exact: X_ixi.
by rewrite -(x_unique _ Xxi (esym fxiy)).
Qed.

End lemma1.

Section lemma2.
Context {R : realType}.
Variable a b : R.
Hypotheses ab : a < b.

Variable F : {fun `[a, b]%classic >-> [set: R]}.
Variable ndF : {in `[a, b]%classic &, nondecreasing_fun F}.
Let B := not_subset01 F.

(* Lemma 2 (i) *)
Lemma is_countable_not_subset01_nondecreasing_fun : countable B.
Proof.
pose x1 (y : R) : R := inf (`[a, b] `&` F @^-1` [set y]).
pose x2 (y : R) := sup (`[a, b] `&` F @^-1` [set y]).
pose B_ := fun (n : nat) => B `&` [set y | x2 y - x1 y > (b - a) / n.+1%:R].
have x1x2 n y : B_ n y -> x1 y < x2 y.
  move=> [By] /=.
  rewrite ltrBrDr.
  apply: lt_trans.
  rewrite ltrDr.
  apply: divr_gt0 => //.
  by rewrite ltrBrDr add0r.
have Uab n: \bigcup_(y in B_ n) `]x1 y, x2 y[%classic `<=` `[a, b].
  apply: bigcup_sub.
  move=> y [[[[+ _]]] _].
  move=> [x /=[xab <-{y}]].
  apply: subset_itvW.
  - apply: lb_le_inf; first by exists x.
    move=> r /= [+ _].
    by rewrite in_itv/= => /andP[+ _].
  - apply: sup_le_ub; first by exists x.
    move=> r /= [+ _].
    by rewrite in_itv/= => /andP [_ +].
have a1y y : a <= x1 y.
  admit.
have y2b y : x2 y <= b.
  admit.
have x1x2F y : B y -> `]x1 y, x2 y[ `<=` F @^-1` [set y].
  rewrite /B /not_subset01/= => -[_ [Fy0]].
  move=> /existsNP[s1] /existsNP[s2].
  move=> /not_implyP[[/= s1ab Fs1r]] /not_implyP[[s2ab Fs2r]] /eqP s1s2.
  have [u [uoo sdu Fu]] : exists u : R^nat,
      [/\ u n @[n --> \oo] --> x1 y, decreasing_seq u & forall n, F (u n) = y /\ u n > x1 y].
    admit.
  admit.
have finBn n : finite_set (B_ n).
  apply: contrapT.
  move/infiniteP.
  move/pcard_surjP => [/= g surjg].
  set h := 'pinv_(fun=> 0) (B_ n) g.
  have Bnh m : B_ n (h m).
    admit.
  have Bh m : B (h m).
    have := Bnh m.
    by apply: subIsetl.
  have ty : trivIset [set: nat] (fun n => `]x1 (h n), x2 (h n)[%classic).
    apply: ltn_trivIset => m1 m2 m12.
    have : h m1 != h m2.
      apply/eqP.
      rewrite /h.
      move=> /(f_equal g).
      rewrite !pinvK => //.
          apply/eqP.
          by rewrite gt_eqF.
        rewrite inE.
        move: surjg.
        rewrite surjE.
        move/(_ m2).
        exact.
      rewrite inE.
      move: surjg.
      rewrite surjE => /(_ m1).
      exact.
    move=> neqhm12.
    apply: (subsetI_eq0 (x1x2F (h m2) (Bh m2)) (x1x2F (h m1) (Bh m1))).
    have := (@preimage_setI_eq0 _ _ (Fun.sort F) [set h m2] [set h m1]).
    move=> [+ _].
    apply.
    apply: preimage0eq.
    rewrite -subset0 => x /= [->].
    move/esym/eqP.
    by apply/negP.
  have : ((\sum_(n <oo) ((x2 (h n) - x1 (h n))%:E)) < (b - a)%:E)%E.
    (* by Uab, ty *)
    admit.
  have : ((\sum_(n <oo) ((x2 (h n) - x1 (h n))%:E)) = +oo%E )%E.
    (* by ty, def of B_ n *)
    admit.
  by move=> ->.
have -> : B = \bigcup_n (B_ n).
  apply/seteqP; split.
    move=> x [_ []].
    admit.
  by move=> ? [? _ []].
apply: bigcup_countable => //.
move=> n _.
by apply: finite_set_countable.
Admitted.

(* see lebegue_measure_rat in lebesgue_measure.v *)
Lemma is_borel_not_subset01_nondecreasing_fun : measurable B. (*TODO: right measurable inferred? *)
Proof.
have /countable_bijP[N /pcard_eqP/bijPex [/= g bijg]] := is_countable_not_subset01_nondecreasing_fun.
set h := 'pinv_(fun=> 0) B g.
suff -> : B = \bigcup_(i in N) (set1 (h i)).
  apply: bigcup_measurable => n _.
  exact: measurable_set1.
apply/seteqP; split.
  move=> r Br.
  exists (g r) => //.
    apply: (set_bij_sub bijg).
    by exists r.
  rewrite /h pinvKV ?inE //.
  exact: (set_bij_inj bijg).
move=> _ [n Nn] /= ->.
apply: (set_bij_sub (bijpinv_bij (fun=> 0) bijg)).
by exists n.
Qed.

Lemma delta_set_not_subset01_nondecreasing_fun Z :
  Z `<=` `]a, b[%classic -> Gdelta Z -> measurable (F @` Z). (*TODO: right measurable inferred? *) (* use mu.-cara.-measurable (f @` Z) instead? *)
Proof.
Admitted.

Notation mu := (@lebesgue_measure R).

Lemma measure_image_not_subset01_nondecreasing_fun (G : (set R)^nat) :
  (forall k, open (G k)) ->
  let Z := \bigcap_k (G k) in
  mu (F @` Z) = mu (\bigcap_k F @` G k).
Proof.
Admitted.

End lemma2.

Section lemma3.
Context (R : realType).
Context (a b : R) (ab : a < b).

Local Notation mu := (@completed_lebesgue_measure R).

(* lemma3 (easy direction) *)
Lemma Lusin_image_measure0 (f : R -> R) :
  {within `[a, b], continuous f} ->
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  lusinN `[a, b] f ->
  forall Z : set R, [/\ Z `<=` `[a, b]%classic,
      compact Z &
      mu Z = 0] ->
      mu (f @` Z) = 0.
Proof.
move=> cf ndf lusinNf Z [Zab cZ muZ0].
have /= mZ : (wlength idfun)^*%mu.-cara.-measurable Z.
  by apply: sub_caratheodory; exact: compact_measurable.
exact: (lusinNf Z Zab mZ muZ0).
Qed.

(* lemma3 (converse) *)
Lemma image_measure0_Lusin (f : R -> R) :
  {within `[a, b], continuous f} ->
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  (forall Z : set R, [/\ measurable Z, Z `<=` `[a, b]%classic,
      compact Z,
      mu Z = 0 &
      mu (f @` Z) = 0]) ->
  lusinN `[a, b] f.
Proof.
move=> cf ndf HZ; apply: contrapT.
move=> /existsNP[Z] /not_implyP[Zab/=] /not_implyP[mZ] /not_implyP[muZ0].
move=> /eqP; rewrite neq_lt ltNge measure_ge0/= => muFZ0.
have {}muFZ0 : (mu^*%mu (f @` Z) > 0)%E.
  rewrite measurable_mu_extE//=.
  apply: sub_caratheodory.
  admit.
wlog : Z Zab mZ muZ0 muFZ0 / Gdelta Z.
  admit.
move=> GdeltaZ.
have mfZ : measurable (f @` Z).
  have set_fun_f : set_fun `[a, b] [set: R] f by [].
  pose Hf := isFun.Build R R `[a, b]%classic [set: R] f set_fun_f.
  pose F : {fun `[a, b] >-> [set: R]} := HB.pack f Hf.
  have {}ndf : {in `[a, b]%classic &, {homo f : x y / x <= y}}.
    by move=> x y; rewrite !inE/=; exact: ndf.
  have := @delta_set_not_subset01_nondecreasing_fun R a b ab F ndf _ _ GdeltaZ.
  apply.
  admit. (* ?! *)
have [K [cK KfZ muK]] : exists K, [/\ compact K, K `<=` f @` Z & (0 < mu K)%E].
  admit.
pose K1 := f @^-1` K.
have cK1 : compact K1.
  (* using continuity *)
  admit.
have K1Z : K1 `<=` Z.
  admit.
have fK1K : f @` K1 = K.
  admit.
have [_ _ _ _] := HZ K1.
rewrite fK1K => /eqP; apply/negP.
by rewrite neq_lt muK orbT.
Admitted.

End lemma3.

Section lemma6.
Context (R : realType).
Context (a b : R) (ab : a < b).

Local Notation mu := (@completed_lebesgue_measure R).

(* lemma6(i) *)
Lemma total_variation_Lusin (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] (fun x => fine ((total_variation a ^~ f) x)) ->
  lusinN `[a, b] f.
Proof.
Admitted.

End lemma6.

Section lemma4.
Context (R : realType).
Context (a b : R) (ab : a < b).

Let ex_perfect_set (cmf : cumulative R) (cZ : set R) :
  let f := cmf in
  cZ `<=` `[a, b] ->
  {within `[a, b], continuous f} ->
  {in `[a, b], {homo f : x y / x <= y}} ->
  bounded_variation a b f ->
  exists n, exists I : nat -> R * R,
  (forall i, trivIset setT (fun i => `[(I i).1, (I i).2]%classic) /\
    `](I i).1, (I i).2[ `<=` cZ) /\
     (\sum_(0 <= i < n) `|f (I i).2 - f (I i).1|)%:E
     = completed_lebesgue_stieltjes_measure f cZ.
Proof.
Abort.

End lemma4.

Section lemma6.
Context (R : realType).
Context (a b : R) (ab : a < b).

Local Notation mu := (@completed_lebesgue_measure R).

(* Lemma 6 *)
Lemma Lusin_total_variation (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] f ->
  lusinN `[a, b] (fun x => fine (total_variation a ^~ f x)).
Proof.
move=> cf bvf lf.
have ndt := @total_variation_nondecreasing R a b f.
have ct := total_variation_continuous ab cf bvf.
apply: image_measure0_Lusin => //.
apply: contrapT.
move=> H.
pose TV := (fine \o (total_variation a)^~ f).
have : exists n : nat, (0 < n)%N /\ exists Z_ : `I_ n -> interval R, trivIset setT (fun i => [set` (Z_ i)])
   /\ (0 < mu (TV @` (\bigcup_i [set` Z_ i])))%E
   /\ forall i, [/\ [set` Z_ i] `<=` `[a, b], compact [set` Z_ i] & mu [set` Z_ i] = 0].
  admit.
move=> [n [] n0 [Z_]] [trivZ [Uz0]] /all_and3 [Zab cZ Z0].
pose UZ := \bigcup_i [set` Z_ i].
have UZ_not_empty : UZ !=set0.
  admit.
pose l_ i : R := inf [set` Z_ i].
pose r_ i : R := sup [set` Z_ i].
pose alpha := mu [set (fine \o (total_variation a)^~ f) x | x in UZ].
have rct : right_continuous TV.
  admit.
have monot : {in `[a, b]&, {homo TV : x y / x <= y}}.
  admit.
(*
have : exists n, exists I : (R * R)^nat,
 [/\ (forall i, (I i).1 < (I i).2 /\ `[(I i).1, (I i).2] `<=` `[a, b] ),
     trivIset setT (fun i => `[(I i).1, (I i).2]%classic) &
     \bigcup_(0 <= i < n) (`[(I i).1, (I i).2]%classic) = Z].*)
Admitted.

End lemma6.

Section Banach_Zarecki.
Context (R : realType).
Context (a b : R) (ab : a < b).

Local Notation mu := (@completed_lebesgue_measure R).

(* NB(rei): commented out because it looks like sigma-additivity *)
(*Lemma nondecreasing_fun_image_measure (f : R -> R) (G_ : (set R)^nat) :
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  \bigcap_i G_ i `<=` `]a, b[%classic ->
  mu (\bigcap_i (G_ i)) = \sum_(i \in setT) (mu (G_ i)).
Proof.
Abort.*)

(* Lemma fG_cvg (f : R -> R) (G_ : nat -> set R) (A : set R) *)
(*  : mu (f @` G_ n) @[n --> \oo] --> mu (f @` A). *)
(*   rewrite (_: mu (f @` A) = mu (\bigcap_i (f @` (G_ i)))); last first. *)
(*     rewrite mfA0. *)
(*     apply/esym. *)
(*     have : (mu (\bigcap_(i < n) (f @` (G_ i))) @[n --> \oo] --> mu (\bigcap_i (f @` (G_ i)))). *)
(*       admit. *)
(*     move/cvg_lim => <- //. *)
(*     apply/cvg_lim => //. *)
(*     apply/fine_cvgP; split. *)
(*       admit. *)
(*     apply/cvgrPdist_le => /= d d0. *)
(*     near=> n. *)
(*     rewrite sub0r normrN ger0_norm; last by apply:fine_ge0; rewrite measure_ge0. *)
(*     have n0 : (0 < n)%N by near: n; apply: (nbhs_infty_gt 0). *)

(*     apply: (@squeeze_cvge _ _ _ _ (cst 0) _ (fun i => (2 ^- i)%:E)). *)
(*         near=> n. *)
(*         rewrite measure_ge0 /=. *)
(*         apply: (@le_trans _ _ (mu (\bigcup_(k in [set j | (n.-1 <= j)%N]) (f @` E_ k)))). *)
(*           apply: le_measure => /=. *)
(*               rewrite inE. *)
(*               apply: sub_caratheodory. *)
(*               apply: bigcap_measurable. *)
(*               move=> k _. *)
(*               rewrite image_G. *)
(*               apply: bigcup_measurable. *)
(*               by move=> ? _; apply: mfE. *)
(*             rewrite inE. *)
(*             apply: sub_caratheodory. *)
(*             apply: bigcup_measurable. *)
(*             by move=> k _; apply: mfE. *)
(*           rewrite [X in _ `<=` X](_:_= f @` (G_ n.-1)); last by []. *)
(*           apply: bigcap_inf => /=; first by rewrite ltn_predL. *)
          
(*         admit. *)
(*       by apply: cvg_cst. *)
(*     rewrite -cvg_shiftS /=. *)
(*     apply: cvg_EFin. *)
(*       by near=> n. *)
(*     have Hgeo : (fun n => 2 ^- n.+1) = @geometric R 2^-1 2^-1. *)
(*       apply: funext => n. *)
(*       by rewrite -d_geo. *)
(*     rewrite [X in X @ _ --> _]Hgeo. *)
(*     by apply: cvg_geometric. *)
(*   apply: (@nonincreasing_cvg_mu _ _ R mu (fun i => f @` (G_ i))) => /=. *)
(*         apply: (@le_lt_trans _ _ (f b - f a)%:E). *)
(*           rewrite (_:(f b - f a)%:E = mu `[f a, f b]); last first. *)
(*             rewrite completed_lebesgue_measure_itv. *)
(*             have : f a <= f b. *)
(*               by apply: nndf; rewrite ?in_itv/= ?lexx ?ltW. *)
(*             rewrite le_eqVlt; move/predU1P => [-> |fab]. *)
(*               by rewrite ltxx subrr. *)
(*             by rewrite ifT. *)
(*           apply: le_measure => /=. *)
(*               rewrite inE. *)
(*               apply: sub_caratheodory. *)
(*               rewrite image_G. *)
(*               apply: bigcup_measurable. *)
(*               move=> k _. *)
(*               exact: (mfE k). *)
(*             rewrite inE. *)
(*             by apply: sub_caratheodory. *)
(*           rewrite image_G. *)
(*           move=> y [n _]. *)
(*           move=> [x + <-{y}]. *)
(*           rewrite /E_. *)
(*           move/mem_set/big_ord_setUP => [k abnkx]. *)
(*           apply/andP; split. *)
(*             apply: nndf. *)
(*                 by rewrite in_itv/= lexx ltW. *)
(*               apply: (absub n k (ltn_ord k)) => /=. *)
(*               by rewrite inE in abnkx. *)
(*             move: abnkx. *)
(*             rewrite inE /= in_itv/=. *)
(*             move/andP => [+ _]. *)
(*             move/ltW; apply: le_trans. *)
(*             apply: incl_itv_lb_nat. *)
(*             - exact: ablt. *)
(*             - exact: absub. *)
(*             - by []. *)
(*           apply: nndf. *)
(*               apply: (absub n k (ltn_ord k)) => /=. *)
(*               by rewrite inE in abnkx. *)
(*             by rewrite in_itv/= lexx ltW. *)
(*           move: abnkx. *)
(*           rewrite inE /= in_itv/=. *)
(*           move/andP => [_ +]. *)
(*           move/ltW; move/le_trans; apply. *)
(*           apply: incl_itv_ub_nat. *)
(*           - exact: ablt. *)
(*           - exact: absub. *)
(*           - by []. *)
(*         exact: ltry. *)
(*       move=> i. *)
(*       rewrite image_G. *)
(*       apply: sub_caratheodory. *)
(*       apply: bigcup_measurable. *)
(*       by move=> + _. *)
(*     apply: bigcap_measurable. *)
(*     move=> k _. *)
(*     rewrite image_G. *)
(*     apply: sub_caratheodory. *)
(*     apply: bigcup_measurable. *)
(*     by move=> + _. *)
(*   apply/nonincreasing_seqP. *)
(*   move=> n. *)
(*   rewrite !image_G subsetEset. *)
(*   move=> _ [k /= nk [x] Ekx <-]. *)
(*   exists k => //. *)
(*   by apply: ltnW. *)
(* Admitted. *)

Variable f : R -> R.

Let set_fun_f : set_fun `[a, b]%classic [set: R] f.
Proof. by []. Qed.

HB.instance Definition _ := isFun.Build _ _ _ _ _ set_fun_f.

Let F : {fun `[a, b]%classic >-> [set: R]} := f.

(* lemma7 *)
Lemma Banach_Zarecki_nondecreasing :
  {within `[a, b], continuous f} ->
  {in `[a, b]  &, {homo f : x y / x <= y}} ->
  lusinN `[a, b] f ->
  abs_cont a b f.
Proof.
move=> cf nndf lf; apply: contrapT => /existsNP[e0] /forallNP fe0.
have {fe0} : forall d : {posnum R},
    exists n, exists B : nat -> R * R,
      [/\ (forall i, (i < n)%N -> (B i).1 < (B i).2 /\ `](B i).1, (B i).2[ `<=` `[a, b]),
          trivIset `I_n (fun i => `](B i).1, (B i).2[%classic),
          \sum_(k < n) ((B k).2 - (B k).1) < d%:num &
          \sum_(k < n) (f (B k).2 - f (B k).1) >= e0%:num].
  move=> d; have {fe0} := fe0 d.
  move=> /existsNP[n] /existsNP[B] /not_implyP[] [H1 H2 H3 H4].
  by exists n, B; split => //; rewrite leNgt; apply/negP.
move=> /choice[n_0 ab_0].
pose delta_0 (i : nat) : R := (2 ^+ i.+1)^-1.
have d_geo n : delta_0 n = geometric 2^-1 2^-1 n.
  rewrite /geometric /=.
  rewrite /delta_0.
  by rewrite -exprVn exprS.
have d_geo0 : forall k, (0 < k)%N -> (delta_0 k.-1 = geometric 1 (2 ^-1) k).
  rewrite /geometric /=.
  rewrite /delta_0.
  move=> t t0.
  rewrite prednK //.
  by rewrite -exprVn mul1r.
have delta_0_ge0 (i : nat) : 0 < (2 ^+ i.+1)^-1 :> R by rewrite invr_gt0 exprn_gt0.
pose delta_ (i : nat) : {posnum R} := PosNum (delta_0_ge0 i).
pose n_ i := n_0 (delta_ i).
pose ab_  i := projT1 (cid (ab_0 (delta_ i))).
have ablt i t : (t < n_0 (delta_ i))%N -> (ab_ i t).1 < (ab_ i t).2.
  move=> tn0i.
  move: (projT2 (cid (ab_0 (delta_ i)))).
  move=> [] + _ _ _.
  by move=> /(_ _ tn0i)[+ _].
have absub i t : (t < n_ i)%N -> `](ab_ i t).1, (ab_ i t).2[ `<=` `[a, b].
  move=> tn.
  move: (projT2 (cid (ab_0 (delta_ i)))).
  move=> [+ _ _ _].
  by move/(_ t tn) => [_ +].
have tab_ t : trivIset `I_(n_ t)
    (fun i => `](ab_ t i).1, (ab_ t i).2[%classic).
  move: (projT2 (cid (ab_0 (delta_ t)))).
  by case => _ + _ _ /=.
have Hc n k : (k < n_ n)%N -> {within `[(ab_ n k).1, (ab_ n k).2], continuous f}.
  move=> knn.
  move: cf.
  apply: continuous_subspaceW.
  move=> /= x.
  rewrite !in_itv /=.
  move/andP => [].
  rewrite le_eqVlt.
  move/orP => [/eqP <- _|abnkx xabnk].
    have /= -> := (incl_itv_lb (fun i=> (ablt n (nat_of_ord i) (ltn_ord i)))
      (fun i=> absub n (nat_of_ord i) (ltn_ord i)) (Ordinal knn)).
    have /= := (incl_itv_ub (fun i=> (ablt n (nat_of_ord i) (ltn_ord i)))
      (fun i=> absub n (nat_of_ord i) (ltn_ord i)) (Ordinal knn)).
    apply: le_trans.
    apply/ltW.
    exact: ablt.
  apply/andP; split.
    apply: (le_trans _ (ltW abnkx)).
    by have /= := (incl_itv_lb (fun i=> (ablt n (nat_of_ord i) (ltn_ord i)))
      (fun i=> absub n (nat_of_ord i) (ltn_ord i)) (Ordinal knn)).
  apply: (le_trans xabnk).
  by have /= := (incl_itv_ub (fun i=> (ablt n (nat_of_ord i) (ltn_ord i)))
      (fun i=> absub n (nat_of_ord i) (ltn_ord i)) (Ordinal knn)).
have Hhomo n k :(k < n_ n)%N -> {in `](ab_ n k).1, (ab_ n k).2[ &, {homo f : x y / x <= y}}. 
  move=>knn x y xab yab.
  by apply: nndf; apply: (absub n k).
have d_prop i : \sum_(k < n_ i) (((ab_ i) k).2 - ((ab_ i) k).1) < delta_0 i.
  by rewrite /ab_; case: cid => ? [].
have e0_prop i : \sum_(k < n_ i) (f (((ab_ i) k).2) - f ((ab_ i) k).1) >= e0%:num.
  by rewrite /ab_; case: cid => ? [].
have H3 i k : (k < n_0 (delta_ i))%N ->
    (ab_ i k).1 < (ab_ i k).2 /\ `](ab_ i k).1, (ab_ i k).2[ `<=` `[a, b].
  move=> in0i.
  rewrite /ab_; case: cid => ? [] /=.
  by move/(_ _ in0i).
pose E_ i := \big[setU/set0]_(k < n_ i) `](ab_ i k).1, (ab_ i k).2[%classic.
have mE i : mu.-cara.-measurable (E_ i).
  apply: bigsetU_measurable => /=.
  move=> k _.
  by apply: sub_caratheodory.
pose G_ i := \bigcup_(j in [set j | (j >= i)%N]) E_ j.
have mG i : mu.-cara.-measurable (G_ i) by exact: bigcup_measurable.
pose A := \bigcap_i (G_ i).
have H2 : (@normr R _ 2^-1 < 1)%R by rewrite gtr0_norm// invf_lt1// ltr1n.
have H20 : 1 - 2^-1 != 0 :> R by rewrite lt0r_neq0// subr_gt0; apply: ltr_normlW.
have H1 : (@GRing.inv R 2) / (1 - 2^-1) = 1.
  by rewrite [X in X - _](splitr 1) div1r addrK divff.
have Eled n : (mu (E_ n) <= (delta_0 n)%:E)%E.
  rewrite measure_semi_additive_ord //=; last 3 first.
    move=> k.
    by apply: sub_caratheodory => //=.
    have := tab_ n.
    rewrite trivIset_mkcond/= => /trivIsetP/= tab_n.
    apply/trivIsetP => /= i j _ _ ij.
    have := tab_n i j Logic.I Logic.I ij.
    rewrite ifT; last by rewrite inE/=.
    rewrite ifT; last by rewrite inE/=.
    by [].
    exact: mE.
  apply/ltW.
  under eq_bigr do rewrite completed_lebesgue_measure_itv/= lte_fin ifT // ?(ablt n _ (ltn_ord _))// -EFinD.
  by rewrite sumEFin lte_fin; exact: d_prop.
(* lemma? *)
have image_E : forall i, (f @` (E_ i)) = \big[setU/set0]_(k < n_ i)f @` `](ab_ i k).1, (ab_ i k).2[%classic.
  move=> i.
  apply/seteqP; split => [y/= [x + <-{y}]|].
    rewrite /E_ => /mem_set/big_ord_setUP[j xj].
    apply:set_mem.
    apply/big_ord_setUP; exists j.
    rewrite inE/=.
    exists x => //.
    by rewrite inE in xj.
  move=> y/= /mem_set/big_ord_setUP[j].
  rewrite inE/= => -[x xj] <-{y}.
  exists x => //; rewrite /E_.
  apply:set_mem.
  by apply/big_ord_setUP; exists j; rewrite inE.
have imfitv n k : (k < n_ n)%N -> exists b0 b1,
  (f @` `](ab_ n k).1, (ab_ n k).2[ =
     [set` Interval (BSide b0 (f (ab_ n k).1)) (BSide b1 (f (ab_ n k).2))]).
  move=> knn.
  have := @continuous_nondecreasing_image_itvoo_itv _ (ab_ n k).1 (ab_ n k).2 f.
  by move/(_ (ablt n k knn) (Hc n k knn) (Hhomo n k knn)).
have mimf n k :(k < n_ n)%N -> (R.-ocitv.-measurable).-sigma.-measurable (f @` `](ab_ n k).1, (ab_ n k).2[%classic).
  move=> knn.
  move: (imfitv n k knn) => [b0 [b1]] ->.
  exact: measurable_itv.
have mfE : forall i, (R.-ocitv.-measurable).-sigma.-measurable (f @` (E_ i)).
  move=> i.
  rewrite image_E.
  apply: bigsetU_measurable.
  move=> /= k _.
  exact: mimf.
have image_G : forall i, (f @` (G_ i)) = \bigcup_(k in [set j | (i <= j)%N]) (f @` (E_ k)).
  move=> i.
  apply/seteqP; split => [y/= [x + <-{y}]|].
      move=> [j /= ij Ejx].
      exists j => //=.
      by exists x.
    move=> _ [j /= ij [x Ejx <-]].
    exists x => //.
    by exists j.
have mA0 : mu A = 0.
  rewrite /A.
  have : (mu \o G_) x @[x --> \oo] --> 0%E.
    rewrite /=.
    have : \forall k \near \oo, (cst 0 k <= (mu \o G_) k <= (delta_0 k.-1)%:E)%E.
      near=> k => /=.
      rewrite measure_ge0 /=.
      apply: (@le_trans _ _ (\big[+%E/0%E]_(k <= j <oo) (mu (E_ j))%E)).
      - rewrite (_: G_ k = \bigcup_n G_ (n + k)%N); last first.
          apply/seteqP; split.
          + by exists 0%N.
          + apply: bigcup_sub => n _.
            apply: bigcup_sub => j /= nkj.
            apply: bigcup_sup => /=.
            by rewrite (leq_trans _ nkj)// leq_addl.
          rewrite -nneseries_addn; last by move=> i; by [].
          apply: measure_sigma_subadditive.
              by move=> n; exact: mE.
            by apply: bigcup_measurable => n _; exact: mG.
          move=> x.
          move=> [/= i _] [j /= ikj Ejx].
          exists (j - k)%N => //.
          by rewrite subnK// (leq_trans _ ikj)// leq_addl.
(*      rewrite d_geo0; last by near: k; exists 1%N.*)
      - rewrite [leRHS](_:_ = (\sum_(k <= j <oo) (delta_0 j)%:E)%E); last first.
          apply: esym.
          apply: cvg_lim => //.
          rewrite d_geo0; last by near: k; exists 1%N.
          rewrite /geometric /=.
          rewrite -[X in _ --> (X * _)%:E]H1 mulrAC -exprS.
          rewrite -(cvg_shiftn k) /=.
          rewrite [X in X @ _ --> _](_:_=
         (fun n => (@series R (geometric (2^-1 ^+ k.+1) 2^-1) n)%:E)); last first.
            apply/funext => n.
            rewrite /series /= sumEFin.
            rewrite -{1}(add0n k) big_addn addnK.
            congr (_%:E).
            apply: eq_bigr => i _.
            rewrite -exprD addSn addnC.
            by rewrite /delta_0 -exprVn.
          apply: cvg_EFin; first by apply: nearW.
          by apply: cvg_geometric_series.
        rewrite -nneseries_addn; last by move=> i; apply: measure_ge0.
        rewrite -[leRHS]nneseries_addn; last first.
          move=> i.
          rewrite lee_fin.
          rewrite /delta_0.
          apply/ltW.
          exact: delta_0_ge0.
        apply: lee_lim.
            apply: ereal_nondecreasing_is_cvgn.
            apply: ereal_nondecreasing_series => i _.
            exact: measure_ge0.
          apply: ereal_nondecreasing_is_cvgn.
          apply: ereal_nondecreasing_series => i _.
          rewrite lee_fin.
          rewrite /delta_0.
          apply/ltW.
          exact: delta_0_ge0.
        apply: nearW => /= n.
        exact: lee_sum.
    move/squeeze_cvge.
    apply.
      exact: cvg_cst.
    apply: cvg_trans.
      apply: near_eq_cvg.
      near=> k.
      rewrite d_geo0; last by near: k; exists 1%N.
      reflexivity.
    apply: cvg_EFin; first by near=> k.
    by apply: cvg_geometric.
  suff: (mu \o G_) x @[x --> \oo] --> mu (\bigcap_n G_ n).
    by move=> /cvg_unique /[apply]; exact.
  apply: nonincreasing_cvg_mu => //=.
  - rewrite (@le_lt_trans _ _ (\sum_(0 <= i <oo) mu (E_ i))%E) //.
      apply: measure_sigma_subadditive => //.
      rewrite /G_.
      by apply: bigcup_sub => i _; exact: bigcup_sup.
    apply: (@le_lt_trans _ _ 1%E); last exact: ltry.
    rewrite (_ : 1%E = (\big[+%R/0%R]_(0 <= i <oo) (delta_0 i)%:E)).
      exact: lee_nneseries.
    apply/esym.
    rewrite -H1.
    apply/cvg_lim => //.
    apply: cvg_EFin.
      by apply: nearW => n; rewrite sumEFin.
      under eq_cvg => n.
        rewrite /= sumEFin.
        under eq_bigr do rewrite d_geo.
        over.
    by apply: cvg_geometric_series.
  - by apply: bigcap_measurable => ? _; exact: mG.
  - move=> s k sk.
    rewrite /G_.
    rewrite subsetEset.
    apply: bigcup_sub => n /= kn.
    apply: bigcup_sup => /=.
    exact: (@le_trans _ _ k).
have mfA0 : mu (f @` A) = 0.
  (* use lf *)
  apply: lf.
  + move=> r Ar.
    rewrite /A /bigcap /= /G_ /= in Ar.
    have [i _] := Ar O I.
    rewrite /E_.
    rewrite -bigcup_seq/= => -[j /= Hj].
    by apply: (H3 _ _ _).2.
  + by apply: bigcapT_measurable => //.
  + exact: mA0.
have H n : (e0%:num%:E <= mu (f @` G_ n))%E.
  rewrite image_bigcup.
  have /= := (@bigcup_sup _ _ n [set j | (n <= j)%N] E_).
  move/(_ (leqnn n)).
  move/(@le_measure _ R _ mu) => /=.
  rewrite !inE; move/(_ (mE n)).
  have /= mEn : (((wlength idfun)^*)%mu).-cara.-measurable (\bigcup_(j in [set j | (n <= j)%N]) E_ j).
    by apply: bigcup_measurable => k _ /=.
  move/(_ mEn) => H.
  apply: (@le_trans _ _ (mu (f @` E_ n))) => //.
    rewrite image_E.
    have nndf' : {in `]a, b[ &, {homo f : n m / n <= m}}.
      move=> x y xab yab xy; apply: nndf => //.
      - by move: x xab {xy}; exact/subset_itv_oo_cc.
      - by move: y yab {xy}; exact/subset_itv_oo_cc.
    have [m [fab]] := (get_nice_image_itv ab cf nndf' (ablt n) (absub n) (tab_ n)).
    move=> [fabsub fablt tfab U2fab U2sum].
    rewrite completed_lebesgue_measureE.
    rewrite (_: \big[setU/set0]_(i < n_0 (delta_ n)) (f @` `] (ab_ n i).1,  (ab_ n i).2[%classic) =
          \big[setU/set0]_(i < m) ((fun i : nat => `](fab i).1, (fab i).2[%classic) i)); last first.
      by rewrite U2fab.
    rewrite U2sum.
    by rewrite lee_fin e0_prop.
  apply: le_measure => /=.
      rewrite inE image_E.
      apply: sub_caratheodory.
      apply: bigsetU_measurable => /= k _.
      exact: (mimf n k (ltn_ord k)).
    rewrite inE.
    apply: bigcup_measurable => m /= nm.
    rewrite image_E.
    apply: sub_caratheodory.
    apply: bigsetU_measurable => /= k _.
    exact: (mimf m k (ltn_ord k)).
  move=> _ [x Enx] <-.
  exists n => //=.
  by exists x.
have muFG0 : mu (\bigcap_k [set f x | x in G_ k]) = 0.
  have ndF : {in `[a, b]%classic &, {homo F : n m / n <= m}}.
    by move=> x y /[!inE] xab yab xy; exact: nndf.
  have Gopen k : open (G_ k).
    apply: bigcup_open => i _.
    rewrite /E_ -(bigcup_mkord (n_ i) (fun k => `](ab_ i k).1, (ab_ i k).2[%classic)).
    by apply: bigcup_open => j _; exact: interval_open.
  have := @measure_image_not_subset01_nondecreasing_fun R a b ab F ndF G_ Gopen.
  by rewrite /= -/A -completed_lebesgue_measureE mfA0.
have : (e0%:num%:E <= limn (fun n => mu (F @` G_ n)))%E.
  apply: lime_ge; last exact: nearW.
  apply: ereal_nonincreasing_is_cvgn; apply/nonincreasing_seqP => n.
  rewrite le_measure ?inE //=.
  - by rewrite image_G; apply: sub_caratheodory; exact: bigcup_measurable.
  - by rewrite image_G; apply: sub_caratheodory; exact: bigcup_measurable.
  - apply: image_subset; apply: bigcup_sub => j /= mj x Ejx.
    by exists j => //=; exact: leq_trans mj.
suff: mu (\bigcap_k (f @` G_ k)) = lim (mu (F @` G_ n) @[n --> \oo]).
  by move=> <-; apply/negP; rewrite -ltNge muFG0.
apply/esym/cvg_lim => //=; apply: nonincreasing_cvg_mu => //=.
- apply: (@le_lt_trans _ _ (mu `[F a, F b])); last first.
    rewrite completed_lebesgue_measureE lebesgue_measure_itv//= lte_fin.
    rewrite (lt_neqAle (f a)) nndf ?andbT.
    by case: ifPn => //; rewrite -EFinB ltry.
    by rewrite in_itv/= lexx/= ltW.
    by rewrite in_itv/= lexx/= ltW.
    exact: ltW.
  rewrite le_measure//= ?inE.
    apply: sub_caratheodory; rewrite image_G.
    by apply: bigcup_measurable => p _; exact: mfE.
    exact: sub_caratheodory.
  move=> x/= [r [i _]].
  rewrite /E_ -(bigcup_mkord (n_ i) (fun k => `](ab_ i k).1, (ab_ i k).2[%classic)).
  move=> -[j jni]/= ijr <-{x}.
  apply: continuous_nondecreasing_image_itvcc => //.
  exact: ltW.
  by exists r => //=; exact: (absub _ _ _ _ ijr).
- move=> k; apply: sub_caratheodory; rewrite image_G.
  by apply: bigcup_measurable => p _; exact: mfE.
- apply: sub_caratheodory; apply: bigcap_measurable => p _.
  by rewrite image_G; apply: bigcup_measurable => q _; exact: mfE.
- move=> x y xy; apply/subsetPset; apply: image_subset; rewrite /G_.
  apply: bigcup_sub => i/= yi.
  by apply: bigcup_sup => //=; rewrite (leq_trans xy).
Admitted.

End Banach_Zarecki.

Section banach_zarecki.
Context (R : realType).
Context (a b : R) (ab : a < b).

Local Notation mu := (@completed_lebesgue_measure R).

Theorem Banach_Zarecki (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] f ->
  abs_cont a b f.
Proof.
move=> cf bvf Lf.
apply: total_variation_AC => //.
apply: Banach_Zarecki_nondecreasing => //.
- exact: total_variation_continuous.
- move=> x y; rewrite !in_itv /= => /andP[ax xb] /andP[ay yb] xy.
  apply: fine_le.
  + apply/(bounded_variationP _ ax); exact:(bounded_variationl _ xb).
  + apply/(bounded_variationP _ ay); exact:(bounded_variationl _ yb).
  + by apply: (@total_variation_nondecreasing _ _ b); rewrite ?in_itv /= ?ax ?ay.
- exact: Lusin_total_variation.
Qed.

End banach_zarecki.
