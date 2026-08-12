From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import borel_hierarchy absolute_continuity.
From mathcomp Require Import banach_zarecki_lemma1.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 2)                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section lemma2.
Context {R : realType}.
Variable a b : R.
Variable f : R -> R.

Let homof : {homo f : x / `[a, b]%classic x >-> [set: R] x}.
Proof. by []. Qed.

Local Notation preimages_gt1 := (preimages_gt1 `[a, b] [set: R]).

Let infpre y := inf (`[a, b] `&` f @^-1` [set y]).
Let suppre y := sup (`[a, b] `&` f @^-1` [set y]).

Lemma preimages_gt1_inf_sup y : preimages_gt1 f y
   -> infpre y < suppre y.
Proof.
move=> [_ /= (* [_ +]*)].
apply: has_bound_not_subset1_inf_sup.
  by exists a => z [] /=; rewrite in_itv/= => /andP[].
by exists b => z [] /=; rewrite in_itv/= => /andP[].
Qed.

(* move=> /not_subset1P[x [y [xy abx aby FxFr FyFr]]]. *)
(* wlog : x y abx aby FxFr FyFr xy / x < y. *)
(*   move=> wlg; move: xy; rewrite neq_lt => /orP[xy|yx]. *)
(*     by apply: (wlg _ _ abx aby) => //; rewrite lt_eqF. *)
(*   by apply: (wlg _ _ aby abx) => //; rewrite lt_eqF. *)
(* move=> {}xy; apply: (@le_lt_trans _ _ x). *)
(*   rewrite -(inf1 x); apply: le_inf; last 2 first. *)
(*     by exists x. *)
(*     split; first by exists r. *)
(*     by exists a => z [] /=; rewrite in_itv/= => /andP[]. *)
(*   move=> _ /= [_ -> <-]. *)
(*   by exists (- x); split => //=; exists x. *)
(* apply: (@lt_le_trans _ _ y) => //. *)
(* rewrite -(sup1 y); apply: le_sup; last 2 first. *)
(*   by exists y. *)
(*   split; first by exists r. *)
(*   exists b => z [] /=. *)
(*   by rewrite in_itv/= => /andP[]. *)
(* by rewrite sub1set inE; exists y. *)
(* Qed. *)

Hypotheses ab : a < b.
Variable ndf : {in `[a, b]%R &, nondecreasing_fun f}.

Let B_nonempty r : preimages_gt1 f r
   -> `[a, b] `&` f @^-1` [set r] !=set0.
Proof. by move=> [_ /=/existsNP[x]/existsNP[_ /not_implyP[xr _]]]; exists x. Qed.

(* Lemma 2 (i) *)
Section lemma2i.
Notation mu := lebesgue_measure.

Let ubb r : ubound (`[a, b] `&` f @^-1` [set r]) b.
Proof. by move=> s /= [+ _]; rewrite in_itv/= => /andP[]. Qed.
Let lba r : lbound (`[a, b] `&` f @^-1` [set r]) a.
Proof. by move=> s /= [+ _]; rewrite in_itv/= => /andP[]. Qed.

Let infsuppref y : `]infpre y, suppre y[ `<=` f @^-1` [set y].
Proof.
apply: (@subset_trans _ (`[a, b] `&` f @^-1` [set y])); last exact: subIsetr.
rewrite -[X in _ `<=` X]RhullK; last first.
  rewrite /Rhull /= -/(infpre _) -/(suppre _) !ifT.
  - by apply: asboolT; exists a; exact: lba.
  - by apply: asboolT; exists b; exact: ubb.
  by apply: subset_itvW; rewrite lexx.
rewrite inE => p q/=.
rewrite !in_itv/= => -[/andP[ap pb] Fpy] [/andP[aq qb] Fqy].
move=> r /andP[pr rq].
rewrite in_itv/= (le_trans ap pr)/= (le_trans rq qb)/=; split => //.
apply/eqP; rewrite eq_le; apply/andP; split.
  by rewrite -Fqy ndf// in_itv/= ?aq//= (le_trans ap pr) (le_trans rq qb).
by rewrite -Fpy ndf// in_itv/= ?ap//= (le_trans ap pr) (le_trans rq qb).
Qed.

Let X n :=
  preimages_gt1 f `&` [set y | suppre y - infpre y > (b - a) / n.+1%:R].

Let infsuppre n y : X n y -> infpre y < suppre y.
Proof.
move=> [By] /=; rewrite ltrBrDr; apply: lt_trans.
by rewrite ltrDr divr_gt0// subr_gt0.
Qed.

Let preimages_gt1_bigcup : preimages_gt1 f = \bigcup_n (X n).
Proof.
apply/seteqP; split; last by move=> ? [? _ []].
move=> x Fx.
near \oo => n.
exists n => //; split => //=.
rewrite ltr_pdivrMr// -ltr_pdivrMl.
  by rewrite subr_gt0 preimages_gt1_inf_sup.
rewrite -addn1 natrD -ltrBlDr.
by near: n; exact: nbhs_infty_gtr.
Unshelve. end_near. Qed.

Let Uab n : \bigcup_(y in X n) `]infpre y, suppre y[%classic `<=` `[a, b].
Proof.
apply: bigcup_sub => r B_nr; apply: subset_itvW.
  by apply: lb_le_inf; [apply: B_nonempty; case: B_nr|exact: lba].
by apply: ge_sup; [apply: B_nonempty; case: B_nr|exact: ubb].
Qed.

Let finXn n : finite_set (X n).
Proof.
apply: contrapT => /infiniteP/pcard_surjP[/= g surjg].
set h := 'pinv_(fun=> 0) (X n) g.

have Xnh m : X n (h m) by   exact: (surjpinv_image_sub surjg).
have Bh m : preimages_gt1 f (h m) by have [] := Xnh m.

have : (\sum_(n <oo) ((suppre (h n) - infpre (h n))%:E) <= mu `[a, b])%E.
(* by Uab, ty *)
  rewrite (@eq_eseriesr _ _
        (fun n => lebesgue_measure `]infpre (h n), suppre (h n)[)).
    move=> k _.
    by rewrite lebesgue_measure_itv /= lte_fin (@infsuppre _ _ (Xnh k)) EFinD.
  rewrite [leLHS](_ : _ = lebesgue_measure
        (\bigcup_i `]infpre (h i), suppre (h i)[%classic)).
    apply: cvg_lim => //.
    apply: measure_semi_sigma_additive; last exact: bigcup_measurable.
    - by [].
    - apply: ltn_trivIset => m1 m2 m12.
      have neqhm12 : h m1 != h m2.
        apply/eqP => /(f_equal g).
        rewrite !pinvK => //; [by rewrite inE; exact: surjg..|].
        by apply/eqP; rewrite gt_eqF.
      apply: (subsetI_eq0 (@infsuppref (h m2)) (@infsuppref (h m1))).
      apply: (@preimage_setI_eq0 _ _ f [set h m2] [set h m1]).1.
      apply: preimage0eq.
      rewrite set1I ifF//.
      by apply/negbTE => /=; rewrite notin_setE/=; apply/nesym/eqP.
  rewrite le_measure//= ?inE//=; first exact: bigcup_measurable.
  move=> /= r [m _ infpresupprer].
  by apply: (@Uab n); exists (h m).
suff : (\sum_(n <oo) ((suppre (h n) - infpre (h n))%:E) = +oo)%E.
  by rewrite lebesgue_measure_itv lte_fin ab/= => ->.
have ty : trivIset [set: nat] (fun n => `]infpre (h n), suppre (h n)[%classic).
  apply: ltn_trivIset => m1 m2 m12.
  have neqhm12 : h m1 != h m2.
    apply/eqP => /(f_equal g).
    rewrite !pinvK => //; [by rewrite inE; exact: surjg..|].
    by apply/eqP; rewrite gt_eqF.
  apply: (subsetI_eq0 (@infsuppref (h m2)) (@infsuppref (h m1))).
  apply: (@preimage_setI_eq0 _ _ f [set h m2] [set h m1]).1.
  apply: preimage0eq.
  rewrite set1I ifF//.
  by apply/negbTE => /=; rewrite notin_setE/=; apply/nesym/eqP.
(* by ty, def of B_ n *)
have Hsum : (\sum_(0 <= s <oo) ((b - a) / n.+1%:R)%:E = +oo)%E.
  apply: cvg_lim => //.
  under eq_cvg do rewrite sumEFin.
  apply/cvgeryP.
  apply/cvgryPge => r.
  near=> m.
  rewrite sumr_const_nat subn0 -[X in _ <= X]mulr_natr -ler_pdivrMl.
    by rewrite divr_gt0// subr_gt0.
  by near: m; exact: nbhs_infty_ger.
apply/eqP; rewrite eq_le; apply/andP; split; first exact: leey.
rewrite -Hsum lee_nneseries => // k _.
  by rewrite lee_fin divr_ge0 // subr_ge0 ltW.
by have [_ /= /ltW] := Xnh k.
Unshelve. end_near. Qed.

Lemma is_countable_preimages_gt1_nondecreasing_fun : countable (preimages_gt1 f).
Proof.
rewrite preimages_gt1_bigcup.
by apply: bigcup_countable => // n _; exact: finite_set_countable.
Qed.

Lemma is_borel_preimages_gt1_nondecreasing_fun : measurable (preimages_gt1 f).
 (*TODO: right measurable inferred? *)
Proof.
apply: countable_measurable => //.
by apply: is_countable_preimages_gt1_nondecreasing_fun.
Qed.

End lemma2i.

(* (* unprovable *) *)
(* have bigcapFG : \bigcap_n (F @` (G_ n)) = \bigcap_n (F @` (G' n)). *)
(*   rewrite eqEsubset; split. *)
(*     move=> y/= FGn. *)
(*     move=> n Nn /=. *)
(*     by move: (FGn n Nn) => [x [_ ?] ?]; exists x. *)
(*   (* unprovable direction *) *)
(*   move=> y/= FGn. *)
(*   move=> n Nn/= . *)
(*   move: (FGn n Nn) => [x G'nx Fxy]. *)
(*   have : exists z, `[a, b]%classic z /\ F z = y. *)
(*     have [z] := UG0. *)
(*     rewrite bigcapIr/=[Zab UG'z]. *)
(*     case => + _. *)
(*     move/(_ x). *)
(*     move=> /=. *)
(*     admit. *)
(*   admit. *)
(* have [eq1 eq2] := (@lemma1 _ _ _ F _ G_ (fun i => (@subIsetl _ _ _))). *)
(* (* w.l.o.g. F @` G_ n is a countable union of intervals *) *)
(*  wlog: G_ G_E G0 Gab near_eqG near_capG bigcapG bigcapFG eq1 eq2 / (exists ab_ : nat -> nat -> (R * R), *)
(*       forall n,(forall i, (ab_ n i).1 < (ab_ n i).2) *)
(*         /\ F @` (G_ n) = \bigcup_i `](ab_ n i).1, (ab_ n i).2[%classic). *)
(*   admit. *)
(* move=> [ab_ Hab_]. *)
(* have ab12 n i : (ab_ n i).1 < (ab_ n i).2 by have [+ _] := (Hab_ n). *)
(* rewrite -(setIidPr (\bigcap_i (F @` (G' i))) (F @` \bigcap_i (G' i))).2; last first. *)
(*   move=> _ /= [x G'x <-] n _ /=. *)
(*   by exists x => //; apply: G'x. *)
(* rewrite -setDD. *)
(* apply: measurableD. *)
(*   rewrite -bigcapFG. (* ? *) *)
(*   apply: bigcap_measurable => n _. *)
(*   rewrite (Hab_ n).2. *)
(*   exact: bigcup_measurable => k _. *)
(* apply: countable_lebesgue_measurable. *)
(* apply: (@sub_countable _ _ _ (preimages_gt1 F)); last exact: is_countable_preimages_gt1_nondecreasing_fun. *)
(* apply: subset_card_le. *)
(* rewrite [X in X `<=` _](_:_= \bigcap_i F @` (G_ i) `\` F @` (\bigcap_i (G_ i))); last by rewrite bigcapFG bigcapG. *)
(* have Giab i : G_ i `<=` `[a, b]. *)
(*   rewrite G_E. *)
(*   exact: subIsetl. *)
(* move=> y/=[FGy nFGy]. *)
(* apply: contrapT => nBy. *)
(* apply: nFGy. *)
(* apply: (eq1 y) => /=; by split. *)

Section image_interval_continuous.
Variables (x y : R).
Hypothesis (xy : x < y).
Hypothesis (xyab : `]x, y[ `<=` `]a, b[).
Hypothesis cfxy : {within `[x, y], continuous f}.

Lemma image_itv_bigcup : exists s : nat -> set R,
  (forall i, is_interval (s i)) /\
  f @` `]x, y[ = \bigcup_i (s i).
Proof.
have ndf_itvoo: {in `]x, y[ &, {homo f : n m / n <= m}}.
  move: ndf.
  apply: itv_sub_in2.
  apply: (subset_trans xyab).
  exact: subset_itv_oo_cc.
have [b0 [b1 FxyE]] :=
        continuous_nondecreasing_image_itvoo_itv xy cfxy ndf_itvoo.
exists (bigcup2 [set` Interval (BSide b0 (f x)) (BSide b1 (f y))] set0).
split.
  case => /=.
    exact: interval_is_interval.
  case => //.
  by move=> ?.
by rewrite FxyE bigcup2E setU0.
Qed.

End image_interval_continuous.

Section lemma2iicontinuous.

Lemma measurable_image_ooitv_nondecreasing_fun (x y : R) :
  x < y -> `]x, y[ `<=` `]a, b[ ->
  {within `[x, y] , continuous f} ->
  measurable (f @` `]x, y[).
Proof.
move=> xy xyab cf.
have := (@image_itv_bigcup x y xy xyab cf).
have ndfxy : {in `[x, y]&, {homo f : n m / n <= m}}.
  apply: (@itv_sub_in2 _ _ _ `[a, b]) => //.
  apply: subset_neitv_oocc => //.
  exact: subset_trans (@subset_itv_oo_cc _ _ a b).
move=> [I_ [itvI_ ->]].
apply: bigcup_measurable => n _.
have := @RhullK R (I_ n).
rewrite inE.
move/(_ (itvI_ n)) => <-.
exact: measurable_itv.
Qed.

Lemma measurable_image_open_nondecreasing_fun Z :
  {within `[a, b], continuous f} -> (* too strong? *)
  Z `<=` `]a, b[%classic -> open Z ->
  measurable (f @` Z).
Proof.
move=> cf Zab oZ.
rewrite (open_bigcup_rat oZ).
rewrite image_bigcup.
have := (card_esym card_rat).
move/card_set_bijP => /=[index Hind].
pose invind := 'pinv_(fun => 0%N) [set: nat] index.
have invindK A := (@pinvK _ _ (fun => 0%N) A index).
have Hfun : set_fun [set n | rat.ratr (index n) \in Z] [set q | rat.ratr q \in Z] index.
  by move=> ?/=.
have Hsurj : set_surj [set n | rat.ratr (index n) \in Z] [set q | rat.ratr q \in Z] index.
  move=> x/= Zx.
  exists (invind x).
    rewrite pinvK// inE.
    move: Hind => [_ _].
    rewrite surjE.
    exact.
  rewrite pinvK// inE.
  move: Hind => [_ _].
  rewrite surjE.
  exact.
have -> := (reindex_bigcup index _ _ _ Hfun Hsurj ).
apply: bigcup_measurable => n nZ.
have lbZna : lbound (bigcup_ointsub Z (index n)) a.
  move=> x [A [[_ _ AZ] _]].
  move=> /AZ/Zab/=.
  by rewrite in_itv/= => /andP[/ltW].
have ubZnb : ubound (bigcup_ointsub Z (index n)) b.
  move=> x [A [[_ _ AZ] _]].
  move=> /AZ/Zab/=.
  by rewrite in_itv/= => /andP[_ /ltW].
have neZn : bigcup_ointsub Z (index n) !=set0.
  exists (rat.ratr (index n)).
  rewrite /bigcup_ointsub.
  near (0 : R)^'+ => e'.
  have e'0 : 0 < e' by [].
  pose e : {posnum R} := PosNum e'0.
  have onb := open_nbhs_ball ((rat.ratr (index n)) : R^o) e.
  set B := (ball ((rat.ratr (index n)) : R^o) e%:num).
  have Bn : B (rat.ratr (index n)) by exact: ball_center.
  exists B => //=.
  split => //.
  split.
  - apply: (@ball_open _ R^o) => //.
    rewrite /B ball_itv; exact: interval_is_interval.
  - rewrite /B/e/=.
    near: e'.
    apply: (@open_subball _ R^o) => //.
    by move: nZ; rewrite /= inE.
have : exists l r, [/\ a <= l, l <= r, r <= b & bigcup_ointsub Z (index n) = `]l, r[%classic].
  exists (inf (bigcup_ointsub Z (index n))), (sup (bigcup_ointsub Z (index n))).
  split.
        apply: lb_le_inf => //.
      move: neZn => [z Znz].
      apply: (@le_trans _ _ z).
        apply: ge_inf => //.
        by exists a.
      apply: ub_le_sup => //.
      by exists b.
    exact: ge_sup.
  rewrite {1}(_:bigcup_ointsub _ _ = interior (bigcup_ointsub Z (index n))).
    rewrite eqEsubset; split.
      have := @openE R.
      rewrite eqEsubset => -[+ _].
      apply.
      exact: open_bigcup_ointsub.
    exact: interior_subset.
  rewrite (@interval_bounded_interior _ (bigcup_ointsub _ _)).
        exact: is_interval_bigcup_ointsub.
      by exists a.
    by exists b.
  rewrite eqEsubset.
  by split => x /=; rewrite in_itv/=.
move=> [l [r [al + rb]]] ->.
rewrite le_eqVlt => /orP[/eqP ->|lr].
  by rewrite set_itvoo0 image_set0.
have lrab : `]l, r[ `<=` `]a, b[.
  move=> x/=; rewrite 2!in_itv/= => /andP[lx xr]; apply/andP; split.
  - exact: le_lt_trans lx.
  - exact: lt_le_trans rb.
have cflr : {within `[l, r], continuous f}.
  apply: continuous_subspaceW cf.
  move=> x/=; rewrite 2!in_itv/= => /andP[lx xr]; apply/andP; split.
  - exact: le_trans lx.
  - exact: le_trans rb.
have := @image_itv_bigcup l r lr lrab cflr.
move=> [lrs_ [lrs_itv ->]].
apply: bigcupT_measurable => m.
rewrite -(RhullK (mem_set (lrs_itv m))).
exact: measurable_itv.
Unshelve. all: end_near. Qed.

(* lemma2 (ii) *)
Lemma measurable_image_Gdelta_set_nondecreasing_fun Z :
  {within `[a, b], continuous f} ->
  Z `<=` `]a, b[%classic -> Gdelta Z ->
  measurable (f @` Z). (* not mu.-cara.-measurable (f @` Z) *)
Proof.
(* TODO: lemma *)
have ndf' : {in `[a, b]%classic &, {homo f : n m / n <= m}}.
  move=> x y.
  rewrite !inE/= => xab yab.
  exact: ndf.
have [|] := pselect (Z !=set0); last first.
  move/set0P/negP/negPn/eqP => -> _ _.
  by rewrite image_set0.
move=> Z0 cf + [/= G' oG'].
move/[swap]; move:Z0; move/[swap] => /[dup]ZG' -> G'0 G'ab.
set G_ := fun i => `]a, b[%classic `&` (G' i).
have {oG'}oG i : open (G_ i) by exact: openI.
have {G'0}IG0 : \bigcap_i G_ i !=set0.
  have [x G'x] := G'0.
  exists x.
  split.
    apply: G'ab.
    exact: G'x.
  exact: G'x.
have IGab : \bigcap_i G_ i `<=` `]a, b[.
  apply: subset_trans G'ab.
  apply: subset_bigcap => i _.
  exact: subIsetr.
have -> : \bigcap_i G' i = \bigcap_i G_ i.
  rewrite bigcapIr.
    by exists 0%N.
  by rewrite setIidr//.
move: G'ab => _.
have Gab_cc i : G_ i `<=` `[a, b].
  apply: (@subset_trans _ `]a, b[%classic).
    exact: subIsetl.
  exact: subset_itv_oo_cc.
have mFG k : measurable [set f x | x in G_ k].
  apply: measurable_image_open_nondecreasing_fun => //.
  exact: subIsetl.
have mIFG : measurable (\bigcap_i [set f x | x in G_ i]) by apply: bigcap_measurable.
have [eq1 eq2] := (@lemma1 _ _ _ f nat G_ homof Gab_cc).
apply: measure_squeeze_measurable eq1 eq2.
- apply: measurableD.
    exact: bigcap_measurable.
  apply: countable_measurable => //.
  exact: is_countable_preimages_gt1_nondecreasing_fun.
- exact: mIFG.
- rewrite setDD.
  apply: (@sub_countable _ _ _ (preimages_gt1 f)); last first.
    exact: is_countable_preimages_gt1_nondecreasing_fun.
  apply: subset_card_le.
  exact: subIsetr.
Qed.

Notation mu := (@lebesgue_measure R).

Lemma measure_image_nondecreasing_fun (G : (set R)^nat) :
  (*  \bigcap_k (G k) `<=` `]a, b[ -> *)
  {within `[a, b], continuous f} ->
  (forall k, G k `<=` `]a, b[) ->
  (forall k, open (G k)) ->
  let Z := \bigcap_k (G k) in
  mu (f @` Z) = mu (\bigcap_k f @` G k).
Proof.
have ndF' : {in `[a, b]%classic &, {homo f : n m / n <= m}}.
  move=> x y.
  rewrite !inE/=.
  exact: ndf.
move=> cf Gab oG.
have Gab' : forall k, G k `<=` `[a, b].
  move=> k.
  apply: (@subset_trans _ `]a, b[%classic) => //.
  exact: subset_itv_oo_cc.
have [HSl HSr] := lemma1 homof Gab'.
move=> Z.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: le_outer_measure.
  apply: (subset_trans HSr).
  apply: subset_bigcap => /= i _.
  exact: image_subset.
rewrite [leLHS](_:_= mu (\bigcap_i [set f x | x in G i] `\` preimages_gt1 f)).
  rewrite measureD /=.
        apply: bigcap_measurable => // k _.
        exact: measurable_image_open_nondecreasing_fun.
      exact: is_borel_preimages_gt1_nondecreasing_fun => //.
    apply: (@le_lt_trans _ _ (mu (f @` G 0%N))).
      apply: le_outer_measure.
      exact: (@bigcap_inf _ _ _ setT).
    apply: (@le_lt_trans _ _ (mu (f @` `]a, b[))).
      apply: le_outer_measure.
      apply: image_subset.
      exact: Gab.
    rewrite integral_continuous_nondecreasing_itv //.
      move: ndf.
      apply: itv_sub_in2.
      exact: subset_itv_oo_cc.
    by rewrite -EFinB ltey.
  rewrite [X in (_ - X)%E](_:_ = 0) ?sube0//.
  apply/eqP; rewrite eq_le; apply/andP; split.
    rewrite [leRHS](_:_ = mu (preimages_gt1 f)).
      apply: esym.
      rewrite countable_lebesgue_measure0//.
      exact: is_countable_preimages_gt1_nondecreasing_fun.
    apply: le_outer_measure.
    exact: subIsetr.
  exact: outer_measure_ge0.
exact: le_outer_measure.
Qed.

End lemma2iicontinuous.

End lemma2.
