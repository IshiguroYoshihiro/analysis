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
Lemma bigcap_open (U0_ : (set R)^nat) :
    (forall i : nat, open (U0_ i)) ->
    let U_ := fun i : nat => \bigcap_(j < i) U0_ j
    in (forall i, open (U_ i)).
Proof.
move=> HU U_.
elim.
  rewrite /U_ bigcap_mkord.
  rewrite big_ord0.
  exact: openT.
move=> n IH.
suff -> : U_ n.+1 = U_ n `&` U0_ n by apply: openI.
rewrite /U_.
rewrite !bigcap_mkord.
by rewrite big_ord_recr.
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

Lemma nondecreasing_fun_decomp (a b : R) (f : R -> R) :
  {in `]a, b[ &, {homo f : x y / x <= y}} ->
  forall x, x \in `]a, b[ ->
  \near x, {in `]a, b[ &, {homo f : x y / x < y}} \/ {in `]a, b[ , f =1 cst (f x)}.
Proof.
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
have [fa|fa] := pselect (\forall x \near a^'+, f x = cst (f a) x).
  have [fb|fb] := pselect (\forall x \near b^'-, f x = cst (f b) x).
    exists true, false; apply/seteqP; split => [x/=|x].
    - move=> [r]; rewrite in_itv/= => /andP[ar rb] <-{x}.
      rewrite in_itv/=; apply/andP; split.
(* f a <= f r *)
        by rewrite ndfcc// ?in_itv/= ?lexx ?ltW.
(* f r <= f b *)
      by rewrite ndfcc// ?in_itv/= ?lexx ?ltW.
(* *)
    - rewrite /= in_itv/= => /andP[fax xfb].
      have /(IVT (ltW ab)) : minr (f a) (f b) <= x <= maxr (f a) (f b).
        by rewrite ge_min fax/= le_max xfb orbT.
      move=> /(_ cf)[r].
      rewrite in_itv => /= /andP[].
      rewrite le_eqVlt => /predU1P[<-{r} _ {}fax|].
        near a^'+ => a0.
        exists a0.
          by rewrite in_itv/=; apply/andP; split.
        by near: a0; apply: filterS fa => z ->.
      move=> ar; rewrite le_eqVlt => /predU1P[rb frx|].
        subst x r.
        near b^'- => b0.
        exists b0.
        by rewrite in_itv/=; apply/andP; split.
        by near: b0; apply: filterS fb => z ->.
      move=> rb fxr; exists r => //.
      by rewrite in_itv/= ar rb.
  - exists true, true; apply/seteqP; split => [x/=|x].
      move=> [y]; rewrite in_itv/= => /andP[ay yb] <-{x}.
      rewrite in_itv/=; apply/andP; split.
(* f a <= f y *)
      by rewrite ndfcc// ?in_itv/= ?lexx ?ltW.
(* f y < f b *)
      rewrite lt_neqAle; apply/andP; split; last first.
        move: (fxb) => /cvg_lim <-//.
        apply: limr_ge => //.
          by apply/cvgP; exact: fxb.
        near=> b0.
        apply: ndf.
        - by rewrite in_itv/=; apply/andP; split.
        - by rewrite in_itv/=; apply/andP; split.
        - by near: b0; exact: nbhs_left_ge.
      apply/negP => /eqP fyb.
      apply: fb.
      near=> z.
      rewrite /cst/=.
      have yz : y <= z by near: z; exact: nbhs_left_ge.
      have fyz : f y <= f z.
        apply: ndf => //.
          by rewrite in_itv/= ay yb.
        by rewrite !in_itv/= (lt_le_trans ay yz)//=.
      apply/eqP; rewrite eq_le; apply/andP; split.
        move: (fxb) => /cvg_lim <-//.
        apply: limr_ge => //.
        apply/cvgP; exact: fxb.
        near=> b0.
        apply: ndf.
        - by rewrite in_itv/=; apply/andP; split.
        - by rewrite in_itv/=; apply/andP; split.
        - by near: b0; exact: nbhs_left_ge.
      by rewrite (le_trans _ fyz)// fyb.
(* *)
    - rewrite /= in_itv/= => /andP[fax xfb].
      have /(IVT (ltW ab)) : minr (f a) (f b) <= x <= maxr (f a) (f b).
        by rewrite ge_min fax/= le_max (ltW xfb) orbT.
      move=> /(_ cf)[r].
      rewrite in_itv => /= /andP[].
      rewrite le_eqVlt => /predU1P[<-{r} _ {}fax|].
        near a^'+ => a0.
        exists a0.
          by rewrite in_itv/=; apply/andP; split.
        by near: a0; apply: filterS fa => z ->.
      move=> ar; rewrite le_eqVlt => /predU1P[rb frx|].
        subst x r.
        by rewrite ltxx in xfb.
      move=> rb fxr; exists r => //.
      by rewrite in_itv/= ar rb.
have [fb|fb] := pselect (\forall x \near b^'-, f x = cst (f b) x).
- exists false; exists false; apply/seteqP; split => [x/=|x].
  - move=> [r]; rewrite in_itv/= => /andP[ar rb] <-{x}.
    rewrite in_itv/=; apply/andP; split.
      rewrite lt_neqAle; apply/andP; split; last first.
(* f a <= f r *)
        move: (fxa) => /cvg_lim <-//.
        apply: limr_le => //.
          by apply/cvgP; exact: fxa.
        near=> a0.
        apply: ndf.
        - by rewrite in_itv/=; apply/andP; split.
        - by rewrite in_itv/=; apply/andP; split.
        - by near: a0; exact: nbhs_right_le.
      apply/negP => /eqP far.
      apply: fa.
      near=> z.
      rewrite /cst/=.
      have zr : z <= r by near: z; apply: nbhs_right_le.
      have fzr : f z <= f r.
        apply: ndf => //.
          by rewrite !in_itv/= (le_lt_trans zr rb)//= andbT.
        by rewrite in_itv/= ar rb.
      apply/eqP; rewrite eq_le; apply/andP; split.
        rewrite (le_trans fzr)//.
        by rewrite far.
      move: (fxa) => /cvg_lim <-//.
      apply: limr_le => //.
        apply/cvgP; exact: fxa.
        near=> a0.
        apply: ndf.
        - by rewrite in_itv/=; apply/andP; split.
        - by rewrite in_itv/=; apply/andP; split.
        - by near: a0; apply: nbhs_right_le.
(* f d <= f b *)
    near b^'- => b0.
    have rb0 : r <= b0 by near: b0; apply: nbhs_left_ge.
    have frb0 : f r <= f b0.
      apply: ndf.
      - by rewrite in_itv/=; apply/andP; split.
      - by rewrite in_itv/=; apply/andP; split.
      - by [].
    apply: (le_trans frb0).
    near: b0.
    apply: filterS fb.
    by rewrite /cst => x ->.
  - rewrite /=in_itv/=.
    move/andP => [fax xfb].
    have /(_ x):= (IVT (ltW ab) cf).
    move=> [].
      have fafb : f a < f b by exact: (lt_le_trans fax xfb).
      rewrite /minr/maxr fafb.
      by rewrite (ltW fax).
    move=> r.
    rewrite in_itv/= => /andP [].
    rewrite le_eqVlt; move/orP => [|ar].
      move/eqP => ar _ frx.
      by rewrite ar frx ltxx in fax.
    rewrite le_eqVlt; move/orP => [|rb].
      move/eqP => rb frx.
      near b^'- => z.
      exists z.
        rewrite in_itv/=.
        by apply/andP; split.
      rewrite -frx rb.
      near: z.
      apply: filterS fb.
      by rewrite/cst.
    move=> frx.
    exists r => //.
    by rewrite in_itv/= ar.
- exists false; exists true.
  rewrite eqEsubset; split.
  - move=> x /= [y].
    rewrite in_itv/= => /andP[ay yb] <-{x}.
    rewrite in_itv/=; apply/andP; split.
(* f y < f b *)
      rewrite lt_neqAle; apply/andP; split.
        apply/negP => /eqP fay.
        apply: fa.
        near=> a0.
        rewrite /cst.
        apply/eqP; rewrite eq_le; apply/andP; split.
          rewrite fay.
          apply: ndf.
          - by rewrite in_itv/=; apply/andP; split.
          - by rewrite in_itv/=; rewrite ay.
          near: a0.
          by apply: nbhs_right_le.
        move: (fxa).
        move/cvg_lim <- => //.
        rewrite limr_le //.
          apply: cvgP; exact: fxa.
        near=> x.
        apply: ndf.
        - by rewrite in_itv/=; apply/andP; split.
        - by rewrite in_itv/=; apply/andP; split.
        near: x.
        by apply: nbhs_right_le.
      (* same *)
      move: (fxa).
      move/cvg_lim <- => //.
      rewrite limr_le //.
        exact: cvgP fxa.
      near=> x.
      apply: ndf.
      - by rewrite in_itv/=; apply/andP; split.
      - by rewrite in_itv/=; apply/andP; split.
      near: x.
      by apply: nbhs_right_le.
(* f y < f b *)
    rewrite lt_neqAle; apply/andP; split.
      apply/negP => /eqP fyb.
      apply: (fb).
      near=> b0.
      rewrite /cst.
      apply/eqP; rewrite eq_le; apply/andP; split.
        move: (fxb).
        move/cvg_lim <- => //.
        rewrite limr_ge//.
          exact: cvgP fxb.
        near=> z.
        apply: ndf.
        - by rewrite in_itv/=; apply/andP; split.
        - by rewrite in_itv/=; apply/andP; split.
        near: z.
        by apply: nbhs_left_ge.
      rewrite -fyb.
      apply: ndf.
      - by rewrite in_itv/=; apply/andP; split.
      - by rewrite in_itv/=; apply/andP; split.
      near: b0.
      by apply: nbhs_left_ge.
    move: (fxb).
    move/cvg_lim <- => //.
    rewrite limr_ge //.
      apply: cvgP fxb.
    near=> b0.
    apply: ndf.
    - by rewrite in_itv/=; apply/andP; split.
    - by rewrite in_itv/=; apply/andP; split.
    near: b0.
    by apply: nbhs_left_ge.
  move=> y /=.
  rewrite in_itv/=.
  move/andP => [fay yfb].
  have /(IVT (ltW ab) cf): minr (f a) (f b) <= y <= maxr (f a) (f b).
    by rewrite ge_min le_max (ltW fay) (ltW yfb) orbT.
  move=> [x].
  rewrite in_itv/= => /andP[].
  rewrite le_eqVlt => /orP; case.
    move/eqP => <-{x} _ fay'.
    by move: fay; rewrite fay' ltxx.
  move=> ax.
  rewrite le_eqVlt => /orP; case.
    move/eqP => ->.
    by move: yfb => /[swap] <-; rewrite ltxx.
  move=> xb fxy.
  exists x => //.
  by rewrite in_itv/= ax.
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
- move=> compmu B mB B0 A AB.
  apply: compmu.
  by exists B.
- move=> Hmu A [B [mB B0 AB]].
  by apply: (Hmu B).
Qed.

Section completed_measure_extension.
Local Open Scope ereal_scope.

Context d (T : semiRingOfSetsType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Let Rmu := SetRing.measure mu.
Notation rT := (SetRing.type T).

Let I := [the measurableType _ of caratheodory_type (mu^*)%mu].

Definition completed_measure_extension : set I -> \bar R := (mu^*)%mu.

Local Lemma completed_measure_extension0 : completed_measure_extension set0 = 0.
Proof. exact: mu_ext0. Qed.

Local Lemma completed_measure_extension_ge0 (A : set I) : 0 <= completed_measure_extension A.
Proof. exact: mu_ext_ge0. Qed.

Local Lemma completed_measure_extension_semi_sigma_additive :
  semi_sigma_additive completed_measure_extension.
Proof.
move=> F mF tF mUF; rewrite /completed_measure_extension.
by apply: caratheodory_measure_sigma_additive.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ completed_measure_extension
  completed_measure_extension0 completed_measure_extension_ge0
  completed_measure_extension_semi_sigma_additive.

Lemma completed_measure_extension_sigma_finite : @sigma_finite _ T _ setT mu ->
  @sigma_finite _ _ _ setT completed_measure_extension.
Proof.
move=> -[S setTS mS]; exists S => //; move=> i; split.
  apply: sub_caratheodory.
  apply: sub_sigma_algebra.
  by have := (mS i).1.
by rewrite /completed_measure_extension /= measurable_mu_extE //;
  [exact: (mS i).2 | exact: (mS i).1].
Qed.

(*
d.-cara.-measurable = (d.-measurable `|` [set N | mu' N = 0]).-sigma.-measurable
*)

(* Lemma completed_measure_extension_unique : sigma_finite [set: T] mu ->
  (forall mu' : {measure set I -> \bar R},
    (forall X, d.-measurable X -> mu X = mu' X) ->
    (forall X, (d.-measurable `|` [set N | mu' N = 0]).-sigma.-measurable X ->
      completed_measure_extension X = mu' X)).
Proof.
Abort.
*)

End completed_measure_extension.

Section wlength_completed_extension.
Context {R : realType}.

Definition completed_lebesgue_stieltjes_measure (f : cumulative R) :=
  @completed_measure_extension _ _ _ [the measure _ _ of wlength f].
HB.instance Definition _ (f : cumulative R) :=
  Measure.on (@completed_lebesgue_stieltjes_measure f).

Let sigmaT_finite_completed_lebesgue_stieltjes_measure (f : cumulative R) :
  sigma_finite setT (@completed_lebesgue_stieltjes_measure f).
Proof. exact/completed_measure_extension_sigma_finite/wlength_sigma_finite. Qed.

HB.instance Definition _ (f : cumulative R) := @Measure_isSigmaFinite.Build _ _ _
  (@completed_lebesgue_stieltjes_measure f) (sigmaT_finite_completed_lebesgue_stieltjes_measure f).

End wlength_completed_extension.
Arguments completed_lebesgue_stieltjes_measure {R}.

Definition completed_lebesgue_measure {R : realType} :
  set _ -> \bar R :=
  [the measure _ _ of completed_lebesgue_stieltjes_measure [the cumulative _ of idfun]].
HB.instance Definition _ (R : realType) := Measure.on (@completed_lebesgue_measure R).
HB.instance Definition _ (R : realType) :=
  SigmaFiniteMeasure.on (@completed_lebesgue_measure R).

(* generalize? *)
Lemma completed_lebesgue_measureE {R : realType} :
  (@completed_lebesgue_measure R) = (@lebesgue_measure R).
Proof.
rewrite /completed_lebesgue_measure/=.
rewrite /completed_lebesgue_stieltjes_measure/=.
rewrite /completed_measure_extension/=.
rewrite /lebesgue_measure/=.
rewrite /lebesgue_stieltjes_measure/=.
by rewrite /measure_extension/=.
Qed.

Lemma sigma_algebra_mu_ext {R : realType} :
  sigma_algebra [set: ocitv_type R] ((((wlength idfun)^*)%mu).-cara.-measurable).
Proof.
split.
- exact: caratheodory_measurable_set0.
- by move=> A mA; rewrite setTD; exact: caratheodory_measurable_setC.
- by move=> F mF; exact: caratheodory_measurable_bigcup.
Qed.

Lemma completed_lebesgue_measure_is_complete {R : realType} :
  measure_is_complete (@completed_lebesgue_measure R).
Proof. exact: measure_is_complete_caratheodory. Qed.

(* TODO: fix negligibleI *)
(* TODO 2 spaces in sigma_algebra_bigcup *)
Lemma caratheodory_measurable_mu_ext_new d (R : realType) (T : semiRingOfSetsType d)
    (mu : {measure set T -> \bar R}) A :
  d.-measurable A -> (mu^*)%mu.-cara.-measurable A.
Proof.
by move=> Am; apply: sub_caratheodory => //; apply: sub_sigma_algebra.
Qed.

Definition completed_algebra_gen d {T : semiRingOfSetsType d} {R : realType}
    (mu : set T -> \bar R) : set _ :=
  [set A `|` N | A in d.-measurable & N in mu.-negligible].

Definition completed_algebra d {T : semiRingOfSetsType d} {R : realType}
    (mu : set T -> \bar R) : measurableType _ :=
  salgebraType (completed_algebra_gen mu).

Lemma caratheodory_completed_algebra {R : realType} :
  ((wlength idfun)^*)%mu.-cara.-measurable `<=`
  (completed_algebra_gen (@lebesgue_measure R)).-sigma.-measurable.
Proof.
move=> E.
wlog : E / (completed_lebesgue_measure E < +oo)%E.
  move=> /= wlg.
  have /sigma_finiteP[/= F [UFI ndF mF]] :=
    measure_extension_sigma_finite (@wlength_sigma_finite R idfun).
  move=> mE.
  rewrite -(setIT E)/= UFI setI_bigcupr.
  apply: bigcupT_measurable => i.
  apply: wlg.
    rewrite (le_lt_trans _ (mF i).2)//=.
    rewrite le_measure// inE/=.
      apply: measurableI => //.
      apply: sub_caratheodory.
      exact: (mF i).1.
    apply: sub_caratheodory.
    exact: (mF i).1.
  apply: measurableI => //.
  apply: sub_caratheodory.
  exact: (mF i).1.
move=> mEoo mE.
have inv0 : forall n, 0 < n.+1%:R^-1 :> R.
  by move=> n; rewrite invr_gt0.
set S := [set \big[+%R/0]_(0 <= k <oo) wlength idfun (A k) |
          A in measurable_cover E].
have H1 : forall s : R, 0 < s ->
     exists2 A_ : nat -> set R,
       @measurable_cover _ (ocitv_type R) E A_ &
       (\big[+%R/0%R]_(0 <= k <oo) wlength idfun (A_ k) <
        completed_lebesgue_measure E + s%:E)%E.
  move=> s s0.
  have : lebesgue_measure E \is a fin_num.
    by rewrite ge0_fin_numE//.
  move/lb_ereal_inf_adherent => /(_ _ s0)[_/= [A_ EA_] <-] ?.
  by exists A_ => //.
pose A_ (n : nat) := projT1 (cid2 (H1 _ (inv0 n))).
have mA k : @measurable_cover _ (ocitv_type R) E (A_ k).
  by rewrite /A_; case: cid2.
have mA_E n : (\big[+%R/0%R]_(0 <= k <oo) wlength idfun (A_ n k) <
        completed_lebesgue_measure E + n.+1%:R^-1%:E)%E.
  by rewrite /A_; case: cid2.
pose F_ (n : nat) := \bigcup_m (A_ n m).
have EF_n n : E `<=` F_ n.
  have [/= _] := mA n.
  move=> /subset_trans; apply.
  apply: subset_bigcup => i _.
  done.
have mF_ m : (lebesgue_measure (F_ m) <
             completed_lebesgue_measure E + m.+1%:R^-1%:E)%E.
  apply: (le_lt_trans _ (mA_E m)).
  rewrite /lebesgue_measure/=.
  rewrite /lebesgue_stieltjes_measure/=.
  rewrite /measure_extension/=.
  apply: (le_trans (outer_measure_sigma_subadditive ((@wlength R idfun)^*)%mu (A_ m))).
  apply: lee_nneseries => // n _.
  have := (measurable_mu_extE (@wlength R idfun)) (A_ m n).
  move=> <-//.
  by have [/(_ n)] := mA m.
pose F := \bigcap_n (F_ n).
have FM : @measurable _ (salgebraType R.-ocitv.-measurable) F.
  apply: bigcapT_measurable => k.
  apply: bigcupT_measurable => i.
  apply: sub_sigma_algebra.
  by have [/(_ i)] := mA k.
have EF : E `<=` F.
  rewrite /F.
  by apply: sub_bigcap.
have muEF : completed_lebesgue_measure E = lebesgue_measure F.
  apply/eqP; rewrite eq_le; apply/andP; split.
    by rewrite le_outer_measure.
  apply/lee_addgt0Pr => /= _/posnumP[e].
  near \oo => n.
  apply: (@le_trans _ _ (lebesgue_measure (F_ n))).
    apply: le_outer_measure.
    by apply: bigcap_inf.
  apply: (le_trans (ltW (mF_ n))).
  rewrite leeD// lee_fin.
  apply/ltW.
  by near: n; apply: near_infty_natSinv_lt.
(* G *)
have H2 : forall s : R, 0 < s ->
     exists2 A_ : nat -> set R,
       @measurable_cover _ (ocitv_type R) (F `\` E) A_ &
       (\big[+%R/0%R]_(0 <= k <oo) wlength idfun (A_ k) <
        completed_lebesgue_measure (F `\` E) + s%:E)%E.
  move=> s s0.
  have : lebesgue_measure (F `\` E) \is a fin_num.
    rewrite ge0_fin_numE// (@le_lt_trans _ _ (lebesgue_measure F))//.
    apply: le_outer_measure.
    exact: subDsetl.
    by rewrite -muEF.
  move/lb_ereal_inf_adherent => /(_ _ s0)[_/= [B_ FEB_] <-] ?.
  by exists B_ => //.
pose B_ (n : nat) := projT1 (cid2 (H2 _ (inv0 n))).
have mB k : @measurable_cover _ (ocitv_type R) (F `\` E) (B_ k).
  by rewrite /B_; case: cid2.
have mB_FE n : (\big[+%R/0%R]_(0 <= k <oo) wlength idfun (B_ n k) <
        completed_lebesgue_measure (F `\` E) + n.+1%:R^-1%:E)%E.
  by rewrite /B_; case: cid2.
pose G_ (n : nat) := \bigcup_m (B_ n m).
have FEG_n n : F `\` E `<=` G_ n.
  have [/= _] := mB n.
  move=> /subset_trans; apply.
  apply: subset_bigcup => i _.
  done.
have mG_ m : (lebesgue_measure (G_ m) <
             completed_lebesgue_measure (F `\` E) + m.+1%:R^-1%:E)%E.
  apply: (le_lt_trans _ (mB_FE m)).
  rewrite /lebesgue_measure/=.
  rewrite /lebesgue_stieltjes_measure/=.
  rewrite /measure_extension/=.
  apply: (le_trans (outer_measure_sigma_subadditive ((@wlength R idfun)^*)%mu (B_ m))).
  apply: lee_nneseries => // n _.
  have := (measurable_mu_extE (@wlength R idfun)) (B_ m n).
  move=> <-//.
  by have [/(_ n)] := mB m.
pose G := \bigcap_n (G_ n).
have GM : @measurable _ (salgebraType R.-ocitv.-measurable) G.
  apply: bigcapT_measurable => k.
  apply: bigcupT_measurable => i.
  apply: sub_sigma_algebra.
  by have [/(_ i)] := mB k.
have FEG : F `\` E `<=` G.
  by apply: sub_bigcap.
have muG : lebesgue_measure G = 0.
  transitivity (completed_lebesgue_measure (F `\` E)).
    apply/eqP; rewrite eq_le; apply/andP; split.
      apply/lee_addgt0Pr => _/posnumP[e].
      near \oo => n.
      apply: (@le_trans _ _ (lebesgue_measure (G_ n))).
        apply: le_outer_measure.
        by apply: bigcap_inf.
      apply/ltW.
      apply: (lt_le_trans (mG_ n)).
      rewrite leeD// lee_fin.
      apply/ltW.
      by near: n; apply: near_infty_natSinv_lt.
    by apply: le_outer_measure.
  rewrite measureD//=.
  rewrite setIidr//.
  rewrite muEF subee//.
  rewrite ge0_fin_numE//.
  move: mEoo.
  by rewrite muEF.
  apply: sub_caratheodory.
  done.
  move: mEoo.
  by rewrite muEF.
apply: sub_sigma_algebra.
exists (F `\` G).
  by apply: measurableD => //.
exists (E `&` G).
  apply: (@negligibleS _ _ _ lebesgue_measure G).
  apply: subIsetr.
  by exists G; split => //.
apply/seteqP; split.
  move=> /= x [[Fx Gx]|[]//].
  rewrite -(notK (E x)) => Ex.
  apply: Gx.
  exact: FEG.
move=> x Ex.
have [|FGx] := pselect ((F `\` G) x).
  by left.
right; split => //.
move/not_andP : FGx => [|].
  by have := EF _ Ex.
by rewrite notK.
Unshelve. all: by end_near. Qed.

Lemma setDU {T} (U V W : set T) :
  U `<=` V -> V `<=` W ->
  W `\` U = (W `\` V) `|` (V `\` U).
Proof.
move=> UV VW; apply/seteqP; split.
  move=> x [Wx Ux].
  have [Vx|Vx] := pselect (V x).
    by right.
  by left.
move=> x [[Wx Vx]|[Vx Ux]].
  split => //.
  by move/UV.
split => //.
by apply/VW.
Qed.

Lemma completed_algebraE {R : realType} :
  (completed_algebra_gen (@lebesgue_measure R)).-sigma.-measurable =
  @completed_algebra_gen _ _ R (@lebesgue_measure R).
Proof.
apply/seteqP; split; last first.
  move=> X [/= A /= mA [N neglN]] <-{X}.
  apply: sub_sigma_algebra.
  by exists A => //; exists N.
apply: smallest_sub => //=.
split => /=.
- exists set0 => //.
  exists set0 => //.
    exact: negligible_set0.
  by rewrite setU0.
- move=> G [/= A mA [N negN ANG]].
  case: negN => /= F [mF F0 NF].
  have H1 : ~` G = ~` A `\` (N `&` ~` A).
    rewrite -ANG setCU.
    rewrite setDE.
    rewrite setCI setCK.
    rewrite setIUr.
    by rewrite setICl setU0.
  pose AA := ~` A `\` (F `&` ~` A).
  pose NN := (F `&` ~` A) `\` (N `&` ~` A).
  have H2 : ~` G = AA `|` NN.
    rewrite (_ : ~` G = ~` A `\` (N `&` ~` A))//.
    apply: setDU.
      by apply: setSI.
    by apply: subIsetr.
  exists AA.
    apply: measurableI => //=.
      by apply: measurableC.
    apply: measurableC; apply: measurableI => //.
    by apply: measurableC.
  exists NN.
    exists F; split => //.
    rewrite /NN.
    by move=> x [] [].
  by rewrite setDE setTI.
- move=> F mF/=.
  rewrite /completed_algebra_gen/=.
  pose A n := projT1 (cid2 (mF n)).
  pose N n := projT1 (cid2 (projT2 (cid2 (mF n))).2).
  exists (\bigcup_k A k).
    apply: bigcupT_measurable => i.
    rewrite /A.
    by case: cid2 => //.
  exists (\bigcup_k N k).
  apply: negligible_bigcup => /= k.
  rewrite /N.
  case: (cid2 (mF k)) => //= *.
  by case: cid2 => //.
rewrite -bigcupU.
apply: eq_bigcup => // i _.
rewrite /A /N.
case: (cid2 (mF i)) => //= *.
by case: cid2 => //=.
Qed.

Lemma completed_algebra_caratheodory_aux {R : realType} N :
  (@completed_lebesgue_measure R).-negligible N ->
  ((wlength idfun)^*)%mu.-cara.-measurable N.
Proof.
move=> /= [/= A] [mA A0 NA].
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

Lemma completed_algebra_caratheodory {R : realType} :
  (completed_algebra_gen (@lebesgue_measure R)).-sigma.-measurable `<=`
  ((wlength idfun)^*)%mu.-cara.-measurable.
Proof.
rewrite /=.
have : ((@ocitv R)).-sigma.-measurable `<=`
  ((wlength idfun)^*)%mu.-cara.-measurable.
  rewrite /=.
  move=> x Hx.
  apply: sub_caratheodory.
  move: Hx.
  by apply: sub_sigma_algebra2.
rewrite /=.
move=> h.
rewrite completed_algebraE => A -[/= X mX] [N negN] <-{A}.
apply: measurableU => //; last first.
  apply: completed_algebra_caratheodory_aux.
  case: negN => /= B [mB B0 NB].
  exists B; split => //=.
  apply: sub_caratheodory.
  done.
by apply: sub_caratheodory.
Qed.

Lemma compatible {R : realType} :
  (completed_algebra_gen (@lebesgue_measure R)).-sigma.-measurable =
  ((wlength idfun)^*)%mu.-cara.-measurable.
Proof.
apply/seteqP; split => /=.
  by apply: completed_algebra_caratheodory.
by apply: caratheodory_completed_algebra.
Qed.

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

Section Banach_Zarecki.
Context (R : realType).
Context (a b : R) (ab : a < b).

Local Notation mu := (@completed_lebesgue_measure R).

Lemma total_variation_Lusin (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] (fun x => fine ((total_variation a ^~ f) x)) ->
  lusinN `[a, b] f.
Proof.
Admitted.

Let increasing_points (f : R -> R) :=
  [set y | exists x, x \in `[a, b] /\ f@^-1` [set y] = [set x]].

Lemma nondecreasing_fun_setD_measurable f :
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  mu.-cara.-measurable (`[f a, f b]%classic `\` increasing_points f).
Proof.
Abort.

Lemma nondecreasing_fun_image_Gdelta_measurable (f : R -> R) (Z : set R) :
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  Z `<=` `]a, b[%classic ->
  Gdelta Z ->
  mu.-cara.-measurable (f @` Z).
Proof.
Abort.

Lemma nondecreasing_fun_image_measure (f : R -> R) (G_ : (set R)^nat) :
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  \bigcap_i G_ i `<=` `]a, b[%classic ->
  mu (\bigcap_i (G_ i)) = \sum_(i \in setT) (mu (G_ i)).
Proof.
Abort.

Lemma Lusin_image_measure0 (f : R -> R) :
{within `[a, b], continuous f} ->
  {in `[a, b]&, {homo f : x y / x <= y}} ->
  lusinN `[a, b] f ->
  exists Z : set R, [/\ Z `<=` `[a, b]%classic,
      compact Z,
      mu Z = 0 &
      mu (f @` Z) = 0].
Proof.
Admitted.

Lemma image_measure0_Lusin (f : R -> R) :
{within `[a, b], continuous f} ->
  {in `[a, b]&, {homo f : x y / x <= y}} ->
  (forall Z : set R, [/\ measurable Z, Z `<=` `[a, b]%classic,
      compact Z,
      mu Z = 0 &
      mu (f @` Z) = 0]) ->
  lusinN `[a, b] f.
Proof.
move=> cf ndf clusin.
move=> X Xab mX X0.
Admitted.

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

(* Lemma 6 *)
Lemma Lusin_total_variation (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] f ->
  lusinN `[a, b] (fun x => fine (total_variation a ^~ f x)).
Proof.
move=> cf bvf lf.
have ndt := total_variation_nondecreasing.
have ct :=  (total_variation_continuous ab cf bvf).
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


Lemma Banach_Zarecki_nondecreasing (f : R -> R) :
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
have fG_cvg : mu (f @` G_ n) @[n --> \oo] --> mu (f @` A).
  rewrite (_: mu (f @` A) = mu (\bigcap_i (f @` (G_ i)))); last first.

    admit.
  apply: (@nonincreasing_cvg_mu _ _ R mu (fun i => f @` (G_ i))) => /=.
        apply: (@le_lt_trans _ _ (f b - f a)%:E).
          rewrite (_:(f b - f a)%:E = mu `[f a, f b]); last first.
            rewrite completed_lebesgue_measure_itv.
            have : f a <= f b.
              by apply: nndf; rewrite ?in_itv/= ?lexx ?ltW.
            rewrite le_eqVlt; move/predU1P => [-> |fab].
              by rewrite ltxx subrr.
            by rewrite ifT.
          apply: le_measure => /=.
              rewrite inE.
              apply: sub_caratheodory.
              rewrite image_G.
              apply: bigcup_measurable.
              move=> k _.
              exact: (mfE k).
            rewrite inE.
            by apply: sub_caratheodory.
          rewrite image_G.
          move=> y [n _].
          move=> [x + <-{y}].
          rewrite /E_.
          move/mem_set/big_ord_setUP => [k abnkx].
          apply/andP; split.
            apply: nndf.
                by rewrite in_itv/= lexx ltW.
              apply: (absub n k (ltn_ord k)) => /=.
              by rewrite inE in abnkx.
            move: abnkx.
            rewrite inE /= in_itv/=.
            move/andP => [+ _].
            move/ltW; apply: le_trans.
            apply: incl_itv_lb_nat.
            - exact: ablt.
            - exact: absub.
            - by [].
          apply: nndf.
              apply: (absub n k (ltn_ord k)) => /=.
              by rewrite inE in abnkx.
            by rewrite in_itv/= lexx ltW.
          move: abnkx.
          rewrite inE /= in_itv/=.
          move/andP => [_ +].
          move/ltW; move/le_trans; apply.
          apply: incl_itv_ub_nat.
          - exact: ablt.
          - exact: absub.
          - by [].
        exact: ltry.
      move=> i.
      rewrite image_G.
      apply: sub_caratheodory.
      apply: bigcup_measurable.
      by move=> + _.
    apply: bigcap_measurable.
    move=> k _.
    rewrite image_G.
    apply: sub_caratheodory.
    apply: bigcup_measurable.
    by move=> + _.
  apply/nonincreasing_seqP.
  move=> n.
  rewrite !image_G subsetEset.
  move=> _ [k /= nk [x] Ekx <-].
  exists k => //.
  by apply: ltnW.
move/eqP : mfA0; apply/negP.
rewrite gt_eqF// (@lt_le_trans _ _ e0%:num%:E)//.
move/cvg_lim : (fG_cvg) => <- //.
apply: lime_ge.
  apply: ereal_nonincreasing_is_cvgn.
  apply/nonincreasing_seqP.
  move => n.
  rewrite le_measure ?inE //=.
  - rewrite image_G.
    apply: sub_caratheodory.
    by apply: bigcup_measurable.
  - rewrite image_G.
    apply: sub_caratheodory.
    by apply: bigcup_measurable.
  - apply: image_subset.
    rewrite /G_.
    apply: bigcup_sub => j /= mj.
    move=> x Ejx.
    exists j => //=.
    by apply: leq_trans mj.
  - by apply: nearW.
Admitted.

Theorem Banach_Zarecki (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] f ->
  abs_cont a b f.
Proof.
move=> cf bvf Lf.
apply: total_variation_AC => //.
apply: Banach_Zarecki_nondecreasing.
- exact: total_variation_continuous.
- move=> x y; rewrite !in_itv /= => /andP[ax xb] /andP[ay yb] xy.
  apply: fine_le.
  + apply/(bounded_variationP _ ax); exact:(bounded_variationl _ xb).
  + apply/(bounded_variationP _ ay); exact:(bounded_variationl _ yb).
  + by apply: (@total_variation_nondecreasing _ _ b); rewrite ?in_itv /= ?ax ?ay.
- exact: Lusin_total_variation.
Qed.

End Banach_Zarecki.
