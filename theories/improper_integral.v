Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp Require Import signed reals ereal.
From mathcomp Require Import topology normedtype sequences esum exp.
From mathcomp Require Import measure lebesgue_measure numfun lebesgue_integral.
From mathcomp Require Import itv realfun derive trigo ftc.

From mathcomp Require Import ring lra.

(**md**************************************************************************)
(* # Improper Integral                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* PR? *)
Lemma normr_EFin {R : realType} (x : R) :
  `|x%:E| = (normr x)%:E.
Proof.
have [x0|x0] := (leP 0%R x).
  rewrite gee0_abs; last by rewrite lee_fin.
  by move/normr_idP in x0; rewrite x0.
rewrite lte0_abs; last by rewrite lte_fin.
by rewrite ltr0_norm.
Qed.

Section Rceil_lemma.
Context {R : realType}.

Lemma ler_RceilD (x y : R) :
  (Rceil (x + y) <= Rceil x + Rceil y)%R.
Proof.
Abort.

End Rceil_lemma.

Section near_in_itv_yy_PRed.

Local Import real_interval.

Lemma near_in_itv_oy {R : realFieldType} (a : R) :
  {in `]a, +oo[, forall y, \forall z \near y, z \in `]a, +oo[}.
Proof.
Admitted.

Lemma near_in_itv_yo {R : realFieldType} (b : R) :
  {in `]-oo, b[, forall y, \forall z \near y, z \in `]-oo, b[}.
Proof.
Admitted.

Lemma near_in_itv_yy {R : realFieldType} :
  {in `]-oo, +oo[, forall y : R, \forall z \near y, z \in `]-oo, +oo[}.
Proof.
Admitted.

End near_in_itv_yy_PRed.

Section PRed.
Context {R : realType}.
Local Import set_interval.

Lemma continuous_within_itvcyP (a : R) (f : R -> R) :
  {within `[a, +oo[, continuous f} <->
  {in `]a, +oo[, continuous f} /\ f x @[x --> a^'+] --> f a.
Proof.
Admitted.

Lemma continuous_within_itvycP (b : R) (f : R -> R) :
  {within `]-oo, b], continuous f} <->
  {in `]-oo, b[, continuous f} /\ f x @[x --> b^'-] --> f b.
Proof.
Admitted.

End PRed.

(* Abort? *)
Lemma ge0_Rceil_nat {R : realType} (x : R) : (0 <= x)%R ->
  exists n, n%:R = Rceil x.
Proof.
move=> x0.
have := isint_Rceil x.
  move/RintP => [z cxz].
have : Rceil x \is a int_num.
  rewrite Num.Theory.intrEceil.
  by rewrite Num.Theory.intrKceil.
rewrite Num.Theory.intrEge0; last exact: Rceil_ge0.
move/Num.Theory.natrP => {z cxz}[n cxn].
by exists n.
Restart.
move=> x0.
exists (`|Num.ceil x|)%N.
rewrite natr_absz.
rewrite intr_norm.
rewrite RceilE.
apply/normr_idP.
rewrite ler0z.
rewrite -ceil_ge0.
exact: lt_le_trans x0.
Qed.

(* NB: similar to real_interval.itv_bnd_inftyEbigcup *)
Lemma itvaybig {R : realType} (a : R) :
  `[a%R, +oo[%classic = \bigcup_n `[a%R, a + (@GRing.natmul R 1%R n)]%classic.
Proof.
suff H0 : `[0%R, +oo[%classic = \bigcup_n `[0%R, (@GRing.natmul R 1%R n)]%classic.
  case: (leP a 0%R) => a0.
    rewrite (@set_interval.itv_bndbnd_setU _ _ _ (BLeft 0%R)); last 2 first.
        by rewrite bnd_simp.
      by rewrite bnd_simp.
    rewrite H0//.
    rewrite eqEsubset; split => x.
    - move=> [/=|[n _/=]]; rewrite in_itv/=; move/andP.
      - move=>[ax x0].
        have Na_ge0 : (0 <= @GRing.opp R a)%R by rewrite oppr_ge0.
        have [n na] := ge0_Rceil_nat Na_ge0.
        exists n => //=; rewrite in_itv/= ax/=.
        rewrite ltW//; apply: (lt_le_trans x0).
        by rewrite addrC -(opprK a) subr_ge0 na Rceil_ge.
      move=> [x0 xn].
      have : (0 <= (n%:R) - a)%R.
        rewrite subr_ge0.
        exact: (le_trans a0).
      move/ge0_Rceil_nat => [m mna].
      exists m => //=; rewrite in_itv/=; apply/andP; split.
        exact: (le_trans a0).
      rewrite mna -lerBlDl.
      apply: (@le_trans _ _ (n%:R - a)%R); first exact: lerB.
      exact: Rceil_ge.
    move=> [n _]/=.
    rewrite in_itv/= => /andP[ax xan].
    case: (ltP x 0%R).
      by move=> x0; left; rewrite in_itv/= ax x0.
    move=> x0.
    have := le_trans x0 xan.
    move/ge0_Rceil_nat => [m man].
    right.
    exists m => //=.
    rewrite in_itv/= x0/= man.
    apply: (le_trans xan).
    exact: Rceil_ge.
  rewrite eqEsubset; split => x/=.
    rewrite in_itv/= => /andP[ax _].
    have /ltW := lt_le_trans a0 ax.
    move/ge0_Rceil_nat => [n nx].
    exists n => //=; rewrite in_itv/= nx ax/= ltW//.
    apply: (ltr_pwDl a0).
    exact: Rceil_ge.
  by move=> [? _]/=; rewrite !in_itv/= => /andP[-> _].
rewrite eqEsubset; split.
  move=> x/=.
  rewrite in_itv/= => /andP[x0 _].
  have [n nx] := ge0_Rceil_nat x0.
  exists n => //=.
  by rewrite in_itv/= x0 nx Rceil_ge.
move=> x [n _]/=.
by rewrite !in_itv/= andbT => /andP[].
Qed.

Lemma seqDUE {R : realType} (k : nat) (a : R) :
  seqDU (fun k0 => `]a, (a + k0%:R)%R]%classic) k = `](a + k.-1%:R), (a + k%:R)%R]%classic.
Proof.
rewrite seqDU_seqD/seqD.
  case: k; first by rewrite addr0.
  move=> n.
  rewrite eqEsubset; split => x/=.
  - move=> [].
    rewrite !in_itv/= => /andP[-> ->].
    by move/negP; rewrite negb_and /= real_ltNge//= => ->.
  - rewrite !in_itv/= => /andP[anx xaSn]; split.
    + rewrite xaSn andbT.
      apply: le_lt_trans anx => //.
      by rewrite lerDl ler0n.
    + apply/negP; rewrite negb_and; apply/orP; right.
      by rewrite -real_ltNge//=.
apply/nondecreasing_seqP => n.
rewrite subsetEset => x/=; rewrite !in_itv/=.
move/andP => [-> xan]/=.
apply: (le_trans xan).
by rewrite lerD// ler_nat.
Qed.

Section integral_bigsetU.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma integral_bigsetU_EFin (I : eqType) (F : I -> set T) (f : T -> R)
    (s : seq I) :
  (forall n : I, d.-measurable (F n)) ->
  uniq s ->
  trivIset [set` s] F ->
  let D := \big[setU/set0]_(i <- s) F i in
  measurable_fun D (EFin \o f) ->
  \int[mu]_(x in D) (f x)%:E = (\sum_(i <- s) (\int[mu]_(x in F i) (f x)%:E)).
Proof.
move=> mF; elim: s => [|h t ih] us tF D mf.
  by rewrite /D 2!big_nil integral_set0.
rewrite /D big_cons integral_setU_EFin//.
- rewrite big_cons ih//.
  + by move: us => /= /andP[].
  + by apply: sub_trivIset tF => /= i /= it; rewrite inE it orbT.
  + apply: measurable_funS mf => //; first exact: bigsetU_measurable.
    by rewrite /D big_cons; exact: subsetUr.
- exact: bigsetU_measurable.
- by move/measurable_EFinP : mf; rewrite /D big_cons.
- apply/eqP; rewrite big_distrr/= big_seq big1// => i it.
  move/trivIsetP : tF; apply => //=; rewrite ?mem_head//.
  + by rewrite inE it orbT.
  + by apply/eqP => hi; move: us => /=; rewrite hi it.
Qed.

End integral_bigsetU.

(*============================================================================*)
(* from lang_syntax.v in branch prob_lang_axiom by affeldt-aist *)
(* https://github.com/affeldt-aist/analysis/tree/prob_lang_axiom *)
Section continuous_change_of_variables.
Context {R : realType}.
Let mu := (@lebesgue_measure R).

Lemma lt0_continuous_change_of_variables (F G : R -> R)
   ( a b : R) :
    (a < b)%R ->
    {in `[a, b]&, {homo F : x y / (y < x)%R}} ->
    {within `[a, b], continuous F^`()} ->
    derivable_oo_continuous_bnd F a b ->
    {within `[F b, F a], continuous G} ->
\int[mu]_(x in `[F b, F a]) (G x)%:E = \int[mu]_(x in `[a, b]) (((G \o F) * - (F^`() : R -> R)) x)%:E.
Proof.
Abort.

End continuous_change_of_variables.

(*============================================================================*)
(* from lang_syntax.v in branch prob_lang_axiom by IshiguroYoshihiro *)
(* https://github.com/IshiguroYoshihiro/analysis/tree/prob_lang_axiom *)
Section left_continuousW.

Notation left_continuous f :=
  (forall x, f%function @ at_left x --> f%function x).

Lemma left_continuousW (R : numFieldType) (f : R -> R) :
  continuous f -> left_continuous f.
Proof. by move=> cf x; exact/cvg_at_left_filter/cf. Qed.

End left_continuousW.

Section mv_to_realfun.
Context {R : realType}.

Lemma cvg_dnbhsP (f : R -> R) (p l : R) :
  f x @[x --> p^'] --> l <->
  (forall u : R^nat, (forall n, u n != p) /\ (u n @[n --> \oo] --> p) ->
    f (u n) @[n --> \oo] --> l).
Proof.
split=> [/cvgrPdist_le fpl u [up /cvgrPdist_lt uyp]|H]; last first.
  apply: cvg_at_right_left_dnbhs.
  - by apply/cvg_at_rightP => u [pu uyp]; apply: H; split => // n; rewrite gt_eqF.
  - by apply/cvg_at_leftP => u [pu uyp]; apply: H; split => // n; rewrite lt_eqF.
apply/cvgrPdist_le => e e0.
have [r /= r0 {}fpl] := fpl _ e0.
have [n _ {}uyp] := uyp _ r0.
near=> t; apply: fpl => //=.
apply: uyp.
by near: t; exists n.
Unshelve. all: end_near. Qed.

Lemma cvgr_sub0 T {F : set_system T} {FF : Filter F} (f : T -> R) (k : R) :
  (fun x => f x - k)%R @ F --> 0%R <-> f @ F --> k.
Proof.
split=> [|fFk]; first exact: cvg_zero.
by rewrite -(@subrr _ k)//; apply: cvgB => //; exact: cvg_cst.
Qed.

End mv_to_realfun.

Lemma RintegralD d {T : measurableType d} {R : realType}
  (mu : measure T R) (D : set T) (f1 f2 : T -> R) : measurable D ->
  mu.-integrable D (EFin \o f1) ->
  mu.-integrable D (EFin \o f2) ->
  (\int[mu]_(x in D) (f1 x + f2 x))%R =
  (\int[mu]_(x in D) f1 x + \int[mu]_(x in D) f2 x)%R.
Proof.
move=> mD if1 if2.
by rewrite /Rintegral integralD_EFin// fineD//; exact: integral_fune_fin_num.
Qed.

Lemma RintegralB d {T : measurableType d} {R : realType}
  (mu : measure T R) (D : set T) (f1 f2 : T -> R) : measurable D ->
  mu.-integrable D (EFin \o f1) ->
  mu.-integrable D (EFin \o f2) ->
  (\int[mu]_(x in D) (f1 x - f2 x))%R =
  (\int[mu]_(x in D) f1 x - \int[mu]_(x in D) f2 x)%R.
Proof.
move=> mD if1 if2.
by rewrite /Rintegral integralB_EFin// fineB//; exact: integral_fune_fin_num.
Qed.

(*============================================================================*)
(* my works begin here *)


(* PR *)
Lemma cvg_nbhsP {R: realType} (f : R -> R) (p : R) :
  f x @[x --> p] --> f p <->
  (forall u : R^nat, (u n @[n --> \oo] --> p) ->
    f (u n) @[n --> \oo] --> f p).
Proof.
split=> [/cvgrPdist_le /= fpl u /cvgrPdist_lt /= uyp|pfl].
  apply/cvgrPdist_le.
  move=> e e0.
  move: (fpl e e0).
  move=> [d d0 Hd].
  move: (uyp d d0).
  move=> [m _ Hm].
  exists m => //.
  move=> k mk.
  apply: Hd.
  exact: Hm.
apply: contrapT => fpl; move: pfl; apply/existsNP.
suff: exists2 x : R ^nat,
    x n @[n --> \oo] --> p & ~ f (x n) @[n --> \oo] --> f p.
  by move=> [x_] hp; exists x_; apply/not_implyP.
have [e He] : exists e : {posnum R}, forall d : {posnum R},
    exists xn : R, (`|xn - p| < d%:num)%R /\ (`|f xn - f p| >= e%:num)%R.
  apply: contrapT; apply: contra_not fpl => /forallNP h.
  apply/cvgrPdist_le => e e0; have /existsNP[d] := h (PosNum e0).
  move/forallNP => {}h; near=> t.
  have /not_andP[abs|/negP] := h t.
  - exfalso; apply: abs.
    by near: t;  by exists d%:num => //= z/=; rewrite distrC.
  - by rewrite -ltNge distrC => /ltW.
have invn n : (@GRing.zero R < n.+1%:R^-1)%R by rewrite invr_gt0.
exists (fun n => sval (cid (He (PosNum (invn n))))).
  apply/cvgrPdist_lt => r r0; near=> t.
  rewrite /sval/=; case: cid => x [xpt _].
  rewrite distrC (lt_le_trans xpt)// -(@invrK _ r) lef_pV2 ?posrE ?invr_gt0//.
  near: t; exists `|ceil r^-1|%N => // s /=.
  rewrite -ltnS -(@ltr_nat R) => /ltW; apply: le_trans.
  by rewrite natr_absz gtr0_norm -?ceil_gt0 ?invr_gt0 ?le_ceil ?num_real.
move=> /cvgrPdist_lt/(_ e%:num (ltac:(by [])))[] n _ /(_ _ (leqnn _)).
rewrite /sval/=; case: cid => // x [px xpn].
by rewrite ltNge distrC => /negP.
Unshelve. all: end_near. Qed.

Section itv_interior.
Context {R : realType}.

Lemma itv_interior_bounded (x y : R) (a b : bool) :
(x < y)%R ->
interior [set` (Interval (BSide a x) (BSide b y))] = `]x, y[%classic.
Proof.
move=> xy.
rewrite interval_bounded_interior//; last exact: interval_is_interval.
rewrite inf_itv; last by case: a; case b; rewrite bnd_simp ?ltW.
rewrite sup_itv; last by case: a; case b; rewrite bnd_simp ?ltW.
apply: set_itvoo.
Qed.

Lemma itv_interior_pinfty (x : R) (a : bool) :
interior [set` (Interval (BSide a x) (BInfty _ false))] = `]x, +oo[%classic.
Proof.
rewrite interval_right_unbounded_interior//; first last.
    by apply: hasNubound_itv; rewrite lt_eqF.
  exact: interval_is_interval.
rewrite inf_itv; last by case: a; rewrite bnd_simp ?ltW.
by rewrite set_itv_o_infty.
Qed.

Lemma itv_interior_ninfty (y : R) (b : bool) :
interior [set` (Interval (BInfty _ true) (BSide b y))] = `]-oo, y[%classic.
Proof.
rewrite interval_left_unbounded_interior//; first last.
    by apply: hasNlbound_itv; rewrite gt_eqF.
  exact: interval_is_interval.
rewrite sup_itv; last by case b; rewrite bnd_simp ?ltW.
by apply: set_itv_infty_o.
Qed.

Definition itv_interior :=
  (itv_interior_bounded, itv_interior_pinfty, itv_interior_ninfty).

End itv_interior.

Section decr_derive1.
Local Close Scope ereal_scope.

Context {R: realType}.
Variables (f : R -> R) (x : R).
Variable (D : set R).

(* PR? *)
Lemma decr_derive1_le0 :
  {in (interior D) : set R, forall x : R, derivable f x 1%R} ->
  {in D &, {homo f : x y /~ x < y}} ->
  (interior D) x -> f^`() x <= 0.
Proof.
move=> df decrf Dx.
apply: limr_le.
under eq_fun.
  move=> h.
  rewrite {2}(_:h = h%:A :> R^o); last first.
    by rewrite /GRing.scale/= mulr1.
  over.
  by apply: df; rewrite inE.
have := open_subball (open_interior D) Dx.
move=> [e /= e0 Hball].
have/normr_idP normr2E : @GRing.zero R <= 2 by [].
near=> h.
have hneq0 : h != 0%R by near: h; exact: nbhs_dnbhs_neq.
have Dohx : (interior D) (h + x).
  move: (Hball (`|2 * h|)).
  apply => //.
      rewrite /= sub0r normrN !normrM !normr_id normr2E -ltr_pdivlMl//.
      near: h.
      apply: dnbhs0_lt.
      exact: mulr_gt0.
    by rewrite normrM normr2E mulr_gt0// normr_gt0.
  apply: ball_sym; rewrite /ball/= addrK.
  rewrite normrM normr2E ltr_pMl ?normr_gt0//.
    by rewrite (_:1%R = 1%:R)// ltr_nat.
move: hneq0; rewrite neq_lt => /orP[h0|h0].
+ rewrite nmulr_rle0 ?invr_lt0// subr_ge0 ltW//.
  apply: decrf; rewrite ?in_itv/= ?andbT ?ltW ?gtrDr// inE; exact: interior_subset.
+ rewrite pmulr_rle0 ?invr_gt0// subr_le0 ltW//.
  apply: decrf; rewrite ?in_itv/= ?andbT ?ltW ?ltrDr// inE; exact: interior_subset.
Unshelve. end_near. Qed.

End decr_derive1.

Lemma decr_derive1_le0_itv {R: realType} (f : R -> R) (z : R) (x0 x1 : R) (b0 b1 : bool) :
  {in `]x0, x1[, forall x : R, derivable f x 1%R} ->
  {in (Interval (BSide b0 x0) (BSide b1 x1)) &, {homo f : x y /~ (x < y)%R}} ->
  z \in `]x0, x1[ -> (f^`() z <= 0)%R.
Proof.
have [x10|x01] := leP x1 x0.
  move=> _ _.
  by move/lt_in_itv; rewrite bnd_simp le_gtF.
set itv := Interval (BSide b0 x0) (BSide b1 x1).
move=> df decrf xx0x1.
apply: (@decr_derive1_le0 _ _ _ [set` itv]).
    rewrite itv_interior//.
    by move=> ?; rewrite inE/=; apply: df.
  move=> ? ?; rewrite !inE/=; apply: decrf.
by rewrite itv_interior/=.
Qed.

Lemma in_continuous_mksetr {T : realFieldType} {U : realFieldType}
    (i : interval T) (f : T -> U) :
  {in i, continuous f} -> {in [set` i], continuous f}.
Proof. by move=> fi x; rewrite inE/=; exact: fi. Qed.

Global Hint Extern 0 (open _) => now apply: interval_open : core.
Global Hint Extern 0 ({in [set` _], continuous _}) =>
  now apply: in_continuous_mksetr : core.

Section within_continuous_FTC2_pinfty.
Notation mu := lebesgue_measure.

(* duplication of integral_bigcup,
 * use monotonicity of a seq of sets
 * but disjointness *)
Lemma ge0_nondecreasing_set_cvg_integral {R : realType}
  (S : (set R)^nat) (f : R -> \bar R) :
  {homo S : n m / (n <= m)%N >-> (n <= m)%O} ->
  (forall i, measurable (S i)) ->
  measurable_fun (\bigcup_i S i) f ->
  (forall x, (\bigcup_i S i) x -> 0 <= f x) ->
  ereal_sup (range (fun i => \int[mu]_(x in (S i)) f x)) =
  \int[mu]_(x in \bigcup_i S i) f x.
Proof.
move=> nndS mS mf f0.
have /cvg_lim <- // : \int[mu]_(x in S i) f x @[i --> \oo] -->
    ereal_sup (range (fun i => \int[mu]_(x in S i) f x)).
  apply/ereal_nondecreasing_cvgn/nondecreasing_seqP => n.
  apply: ge0_subset_integral => //=; [exact: mS|exact: mS| | |].
  - by apply: measurable_funS mf; [exact: bigcup_measurable|exact: bigcup_sup].
  - by move=> x Snx; rewrite f0//=; exists n.+1.
  - by rewrite -subsetEset; exact: nndS.
under eq_fun do rewrite integral_mkcond/=.
rewrite -/mu -monotone_convergence//=; last 3 first.
- move=> n; apply/(measurable_restrictT f) => //.
  by apply: measurable_funS mf; [exact: bigcup_measurable|exact: bigcup_sup].
- by move=> n x _; apply: erestrict_ge0 => {}x Snx; apply: f0; exists n.
- move=> x _; apply/nondecreasing_seqP => n; apply: restrict_lee => //.
    by move=> {}x Snx; apply: f0; exists n.+1.
  by rewrite -subsetEset; exact: nndS.
rewrite [RHS]integral_mkcond/=.
apply: eq_integral => /=; rewrite /g_sigma_algebraType/ocitv_type => x _.
transitivity (ereal_sup (range (fun n => (f \_ (S n)) x))).
  apply/cvg_lim => //.
  apply/ereal_nondecreasing_cvgn/nondecreasing_seqP => n; apply: restrict_lee.
    by move=> {}x Snx; apply: f0; exists n.+1.
  by rewrite -subsetEset; exact: nndS.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: ub_ereal_sup => _/= [n _ <-].
  by apply: restrict_lee => //; exact: bigcup_sup.
- rewrite patchE; case: ifPn=> [|/negP].
    rewrite inE => -[n _ Snx].
    apply: ereal_sup_le; exists (f \_ (S n) x) => //.
    by rewrite patchE mem_set.
  rewrite inE -[X in X -> _]/((~` _) x) setC_bigcup => nSx.
  apply/ereal_sup_le; exists point => //=; exists 0%R => //.
  by rewrite patchE memNset//; exact: nSx.
Qed.

Lemma le0_nondecreasing_set_cvg_integral {R : realType}
  (S : nat -> set R) (f : R -> \bar R) :
   {homo S : n m / (n <= m)%N >-> (n <= m)%O} ->
  (forall i, measurable (S i)) ->
  measurable_fun (\bigcup_i S i) f ->
  (forall x, (\bigcup_i S i) x -> f x <= 0) ->
  ereal_inf [set (\int[lebesgue_measure]_(x in (S i)) f x) | i in [set: nat] ] =
     \int[lebesgue_measure]_(x in \bigcup_i S i) f x.
Proof.
move=> incrS mS mf f0.
transitivity (- ereal_sup [set \int[lebesgue_measure]_(x in S i) (fun x => - f x) x | i in [set: nat]]).
  apply/eqP; rewrite eq_le; apply/andP; split.
    admit.
  admit.
transitivity (- \int[lebesgue_measure]_(x in \bigcup_i S i) (fun x => - f x) x); last first.
  admit.
congr (- _).
(* apply: ge0_nondecreasing_set_cvg_integral => //.
  exact: measurableT_comp.
move=> x Sx.
rewrite leeNr oppe0.
exact: f0. *)
Abort.

Local Import real_interval.

Lemma increasing_telescope_sume_infty_fin_num
  (R : realType) (n : nat) (f : nat -> R) :
  limn (EFin \o f) \is a fin_num ->
  {homo f : x y / (x <= y)%N >-> (x <= y)%R} ->
  (\sum_(n <= k <oo) ((f k.+1)%:E - (f k)%:E) = limn (EFin \o f) - (f n)%:E)%E.
Proof.
move=> fin_limf nondecf.
apply/cvg_lim => //.
  have incr_sumf : {homo (fun i => (\sum_(n <= k < i) ((f k.+1)%:E - (f k)%:E)%E)%R) :
    n0 m / (n0 <= m)%N >-> n0 <= m}.
  apply/nondecreasing_seqP => m.
  rewrite -subre_ge0; last first.
    apply/sum_fin_numP => /= ?  _.
    by rewrite -EFinD.
  have [nm|mn]:= ltnP m n.
    rewrite !big_nat !big_pred0//.
      move=> k; apply/andP => -[] /leq_ltn_trans /[apply]; apply/negP.
      by rewrite -leqNgt ltnW.
    move=> k; apply/andP => -[] /leq_ltn_trans /[apply]; apply/negP.
    by rewrite -leqNgt.
  rewrite !telescope_sume//; last exact: leqW.
  by rewrite -EFinB lee_fin subr_ge0 lerB// nondecf.
suff: limn (EFin \o f) - (f n)%:E =
  ereal_sup (range (fun n0 => \sum_(n <= k < n0) ((f k.+1)%:E - (f k)%:E)%E)).
  move=> ->.
  exact: ereal_nondecreasing_cvgn.
transitivity (limn ((EFin \o f) \- cst (f n)%:E)).
  apply/esym.
  apply/cvg_lim => //.
  apply: cvgeB.
  - exact: fin_num_adde_defl.
  - apply: ereal_nondecreasing_is_cvgn.
    by move=> x y xy; rewrite lee_fin; apply: nondecf.
  - exact: cvg_cst.
have := @ereal_nondecreasing_cvgn _ (fun i => \sum_(n <= k < i) ((f k.+1)%:E - (f k)%:E)%E).
move/(_ incr_sumf).
rewrite -(cvg_restrict n (EFin \o f \- cst (f n)%:E)).
move/cvg_lim => <-//.
apply: congr_lim.
apply/funext => k/=.
case: ifP => //.
move/negbT.
rewrite -ltnNge => nk.
under eq_bigr do rewrite EFinN.
by rewrite telescope_sume// ltnW.
Qed.

Lemma ge0_within_pinfty_continuous_FTC2 {R : realType} (f F : R -> R) a (l : R) :
  (forall x, a <= x -> 0 <= f x)%R ->
  F x @[x --> +oo%R] --> l ->
  {within `[a, +oo[, continuous f} ->
  (forall x, a < x -> derivable F x 1)%R -> F x @[x --> a^'+] --> F a ->
  (* TODO: introduce derivable_oo_continuous_bnd F a +oo *)
  {in `]a, +oo[, F^`() =1 f} ->
  (\int[mu]_(x in `[a, +oo[) (f x)%:E = l%:E - (F a)%:E)%E.
Proof.
move=> f_ge0 Fxl /continuous_within_itvcyP[cf fa](*TODO: avoid this?*) dF Fa dFE.
rewrite -integral_itv_obnd_cbnd; last exact: open_continuous_measurable_fun.
rewrite itv_bnd_infty_bigcup seqDU_bigcup_eq.
rewrite ge0_integral_bigcup//=; last 3 first.
- by move=> k; apply: measurableD => //; exact: bigsetU_measurable.
- rewrite -seqDU_bigcup_eq -itv_bnd_infty_bigcup; apply: measurableT_comp => //.
  exact: open_continuous_measurable_fun.
- move=> x/=; rewrite -seqDU_bigcup_eq -itv_bnd_infty_bigcup/=.
  by rewrite /= in_itv/= => /andP[/ltW + _]; rewrite lee_fin; exact: f_ge0.
have dFEn n : {in `]a + n%:R, a + n.+1%:R[, F^`() =1 f}.
  apply: in1_subset_itv dFE.
  apply: subset_trans (subset_itvl _) (subset_itvr _) => //=.
  by rewrite bnd_simp lerDl.
have Fshiftn_liml : limn (EFin \o (fun k => F (a + k%:R))) = l%:E.
  apply/cvg_lim => //.
  apply: cvg_EFin; first exact: nearW.
  apply/((cvg_pinftyP F l).1 Fxl)/cvgryPge => r.
  by near do rewrite -lerBlDl; exact: nbhs_infty_ger.
transitivity (\sum_(0 <= i <oo) ((F (a + i.+1%:R))%:E - (F (a + i%:R))%:E)).
  transitivity (\sum_(0 <= i <oo)
      \int[mu]_(x in seqDU (fun k => `]a, (a + k%:R)]%classic) i.+1) (f x)%:E).
    apply/cvg_lim => //; rewrite -cvg_shiftS/=.
    under eq_cvg.
      move=> k /=; rewrite big_nat_recl//.
      rewrite /seqDU addr0 set_itvoc0// set0D integral_set0 add0r.
      over.
    apply: cvg_toP => //; apply: is_cvg_nneseries => n _.
    rewrite integral_ge0//= => x []; rewrite in_itv/= => /andP[/ltW + _] _.
    by rewrite lee_fin; exact: f_ge0.
  apply: eq_eseriesr => n _.
  rewrite seqDUE/= integral_itv_obnd_cbnd; last first.
    apply: (@measurable_fun_itv_oc _ _ _ false true).
    apply: open_continuous_measurable_fun => // x.
    rewrite inE/= in_itv/= => /andP[anx _].
    by apply: cf; rewrite in_itv//= andbT (le_lt_trans _ anx)// lerDl.
  apply: continuous_FTC2 (dFEn n).
  - by rewrite ltrD2l ltr_nat.
  - have : {within `[a, +oo[, continuous f} by exact/continuous_within_itvcyP.
    apply: continuous_subspaceW.
    apply: subset_trans (subset_itvl _) (subset_itvr _) => //=.
    by rewrite bnd_simp lerDl.
  - split => /=.
    + move=> x; rewrite in_itv/= => /andP[anx _].
      by apply/dF; rewrite (le_lt_trans _ anx)// lerDl.
    + move: n => [|n]; first by rewrite addr0.
      have : {within `[a + n.+1%:R, a + n.+2%:R], continuous F}.
        apply: derivable_within_continuous => /= x.
        rewrite in_itv/= => /andP[aSn _].
        by apply: dF; rewrite (lt_le_trans _ aSn)// ltrDl.
      move/continuous_within_itvP.
      by rewrite ltrD2l ltr_nat ltnS => /(_ (ltnSn _))[].
  - have : {within `[a + n%:R + 2^-1, a + n.+1%:R], continuous F}.
      apply: derivable_within_continuous => x.
      rewrite in_itv/= => /andP[aSn _].
      by apply: dF; rewrite (lt_le_trans _ aSn)// -addrA ltrDl ltr_wpDl.
    move/continuous_within_itvP.
    suff: (a + n%:R + 2^-1 < a + n.+1%:R)%R by move=> /[swap] /[apply] => -[].
    by rewrite -[in ltRHS]natr1 addrA ltrD2l invf_lt1// ltr1n.
rewrite increasing_telescope_sume_infty_fin_num.
- by rewrite addr0 EFinN; congr (_ - _).
- by rewrite Fshiftn_liml.
- apply/nondecreasing_seqP => n; rewrite -subr_ge0.
  have isdF (x : R) : x \in `]a + n%:R, a + n.+1%:R[ -> is_derive x 1%R F (f x).
    rewrite in_itv/= => /andP[anx _].
    rewrite -dFE; last by rewrite in_itv/= andbT (le_lt_trans _ anx)// lerDl.
    rewrite derive1E.
    by apply/derivableP/dF; rewrite (le_lt_trans _ anx)// lerDl.
  have [| |r ranaSn ->] := MVT _ isdF.
  - by rewrite ltrD2l ltr_nat.
  - move : n isdF => [_ |n _].
    + have : {within `[a, +oo[, continuous F}.
        apply/continuous_within_itvcyP; split => // x.
        rewrite in_itv/= andbT => ax.
        by apply: differentiable_continuous; exact/derivable1_diffP/dF.
      by apply: continuous_subspaceW; rewrite addr0; exact: subset_itvl.
    + apply: derivable_within_continuous => x; rewrite in_itv/= => /andP[aSnx _].
      by apply: dF; rewrite (lt_le_trans _ aSnx)// ltrDl.
  - move: ranaSn; rewrite in_itv/= => /andP[/ltW anr _].
    rewrite mulr_ge0//; last by rewrite subr_ge0 lerD2l ler_nat.
    by rewrite f_ge0// (le_trans _ anr)// lerDl.
Unshelve. end_near. Qed.

(* need to generalize l : \bar R? *)
Lemma le0_within_pinfty_continuous_FTC2 {R : realType} (f F : R -> R) a (l : R) :
  (forall x, (a <= x)%R -> f x <= 0)%R ->
  F x @[x --> +oo%R] --> l ->
  {within `[a, +oo[, continuous f} ->
  (* f x @[x --> a^'+] --> f a ->
  (forall x, (a < x)%R -> {for x, continuous f}) -> *)
  (* derivable_oo_continuous_bnd F a +oo *)
  (F x @[x --> a^'+] --> F a) ->
  (forall x, (a < x)%R -> derivable F x 1) ->
  {in `]a, +oo[, F^`() =1 f} ->
  (\int[lebesgue_measure ]_(x in `[a, +oo[) (f x)%:E = l%:E - (F a)%:E)%E.
Proof.
move=> f_ge0 Fl /continuous_within_itvcyP[cf fa] Fa dF dFE.
rewrite -[LHS]oppeK.
rewrite -integralN/=; last first.
  rewrite adde_defN.
  apply: ge0_adde_def => //=; rewrite inE.
    rewrite oppe_ge0.
    rewrite le_eqVlt.
    apply/predU1P; left.
    apply: integral0_eq.
    move=> /= x; rewrite in_itv/= => /andP[ax _].
    rewrite /funepos -EFin_max.
    rewrite /maxr; case: ifP => //.
    move/negP/negP; rewrite -leNgt.
    rewrite le_eqVlt => /predU1P[<- //|].
    move: (f_ge0 x ax).
    rewrite leNgt.
    by move/negP.
  apply: integral_ge0 => /= x.
  rewrite in_itv/= => /andP[ax _].
  rewrite /funeneg.
  rewrite /maxe.
  case: ifP => // _.
  rewrite oppe_ge0 lee_fin.
  exact: f_ge0.
rewrite (@ge0_within_pinfty_continuous_FTC2 _ (- f)%R (- F)%R _ (- l)%R).
- rewrite oppeB//.
  by rewrite EFinN oppeK.
- move=> x ax.
  by rewrite oppr_ge0 f_ge0.
- by apply: cvgN.
- rewrite continuous_within_itvcyP; split.
    by move=> x ax; apply/continuousN/cf.
  exact: cvgN.
- by move=> x ax; exact/derivableN/dF.
- exact: cvgN.
- move=> x; rewrite in_itv/= andbT => ax.
  rewrite derive1E deriveN; last exact: dF.
  congr -%R.
  rewrite -derive1E.
  by apply: dFE; rewrite in_itv/= andbT.
Qed.

End within_continuous_FTC2_pinfty.

Section improper.
Context {R : realType}.

Let itv_bnd_infty_bigcup_seq_pinfty (a0 : R) (b b': bool) (a_ : nat -> R) :
  (a0 < a_ 0%N)%R ->
  {homo a_ : n m / (n <= m)%N >-> (n <= m)%R} ->
  a_ n @[n --> \oo] --> +oo%R ->
  [set` (Interval (BSide b a0) (BInfty _ false))] =
     \bigcup_i [set` (Interval (BSide b a0) (BSide b' (a_ i)))] :> set R.
Proof.
move=> a0a0 incra ay.
rewrite eqEsubset; split; last first.
  by move=> /= x [n _]/=; rewrite !in_itv => /andP[->].
rewrite itv_bnd_infty_bigcup.
move=> x [n _]/=; rewrite in_itv/= => /andP[ax xan].
move: ay.
have [m anam] : exists m, (a0 + n%:R < a_ m)%R.
(*  
exists m => //=.
rewrite in_itv/= ax/=.
by case: b'; rewrite /= ?ltW// (le_lt_trans xan).*)
Abort.

End improper.

Section improper_old.
Context {R : realType}.

(* NB: look too much like itv_bnd_infty_bigcup *)
Let itv_bnd_infty_bigcupS :
  `[0%R, +oo[%classic = \bigcup_i `[0%R, i.+1%:R]%classic :> set R.
Proof.
rewrite eqEsubset; split; last first.
  by move=> /= x [n _]/=; rewrite !in_itv/= => /andP[->].
rewrite itv_bnd_infty_bigcup => z [i _ /= zi].
exists i => //=.
apply: subset_itvl zi.
by rewrite bnd_simp/= add0r ler_nat.
Qed.

Variable mu : {measure set [the measurableType (R.-ocitv.-measurable).-sigma of
  g_sigma_algebraType (R.-ocitv.-measurable)] -> \bar R}.

Let ereal_sup_integral (f : R -> R) :
  (forall x, 0 <= f x)%R -> measurable_fun setT f ->
  \int[mu]_(x in `[0%R, +oo[) (f x)%:E =
  ereal_sup [set \int[mu]_(x in `[0%R, i.+1%:R]) (f x)%:E | i in [set: nat]].
Proof.
move=> f0 mf.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ub_ereal_sup => /=_ [n _ <-].
  apply: ge0_subset_integral => //=.
  - apply/measurable_EFinP.
    exact: measurable_funS mf.
  - by move=> ? _; rewrite lee_fin f0.
  - exact: subset_itvl.
rewrite itv_bnd_infty_bigcupS seqDU_bigcup_eq ge0_integral_bigcup//; last 3 first.
- move=> ?.
  apply: measurableD => //.
  exact: bigsetU_measurable.
- apply: measurable_funTS.
  exact/measurable_EFinP.
- by move=> x; rewrite lee_fin f0//.
apply: lime_le => /=.
  apply: is_cvg_nneseries => n _.
  apply: integral_ge0 => k _.
  exact: f0.
apply: nearW => n.
rewrite -ge0_integral_bigsetU//=; first last.
- by move=> ? _; rewrite lee_fin ?expR_ge0.
- apply/measurable_EFinP.
  exact: measurableT_comp.
- exact: (@sub_trivIset _ _ _ [set: nat]).
- exact: iota_uniq.
- move=> k.
  apply: measurableD => //.
  exact: bigsetU_measurable.
rewrite -/mu.
rewrite big_mkord.
rewrite -bigsetU_seqDU.
move: n => [|n].
  rewrite big_ord0 integral_set0.
  apply: ereal_sup_le.
  exists (\int[mu]_(x in `[0%R, 1%:R]) (f x)%:E) => //.
  apply: integral_ge0.
  by move=> ? _; rewrite lee_fin f0.
rewrite [X in \int[_]_(_ in X) _](_ : _ = `[0%R, n.+1%:R]%classic); last first.
  rewrite eqEsubset; split => x/=; rewrite in_itv/=.
    rewrite -(bigcup_mkord _ (fun k => `[0%R, k.+1%:R]%classic)).
    move=> [k /= kSn].
    rewrite in_itv/= => /andP[-> xSk]/=.
    by rewrite (le_trans xSk)// ler_nat.
  move=> /andP[x0 Snx].
  rewrite -(bigcup_mkord _ (fun k => `[0%R, k.+1%:R]%classic)).
  exists n => //=.
  by rewrite in_itv/= x0 Snx.
apply: ereal_sup_le.
exists (\int[mu]_(x in `[0%R, n.+1%:R]) (f x)%:E).
  by exists n.
apply: ge0_subset_integral => //=.
  apply/measurable_EFinP.
  exact: measurableT_comp.
by move=> ? _; rewrite lee_fin f0.
Qed.

Lemma ge0_limn_integraly (f : R -> R) :
  (forall x, 0 <= f x)%R -> measurable_fun setT f ->
  (fun n => \int[mu]_(x in `[0%R, n%:R]) (f x)%:E) @ \oo -->
  \int[mu]_(x in `[0%R, +oo[) (f x)%:E.
Proof.
move=> f0 mf.
rewrite -cvg_shiftS/= ereal_sup_integral//.
apply/ereal_nondecreasing_cvgn/nondecreasing_seqP => n.
apply: (@ge0_subset_integral _ _ _ mu) => //.
- by apply: measurable_funTS; exact: measurableT_comp.
- by move => ? _; apply: f0.
- by apply: subset_itvl; rewrite bnd_simp ler_nat.
Qed.

End improper_old.

Section Gamma.
Context {R : realType}.

Let mu := @lebesgue_measure R.

(* NB: also defined in prob_lang_wip*)
Definition Gamma (a : R) : \bar R :=
  (\int[mu]_(x in `[0%R, +oo[) (powR x (a - 1) * expR (- x))%:E)%E.

Let I n := \int[mu]_(x in `[0%R, +oo[) (x ^+ n * expR (- x))%:E.

Let I0 : I O = 1.
Proof.
rewrite /I.
(under eq_integral do rewrite expr0 mul1r) => /=.
have expRN1 : (fun x => @expR R (- x)) = fun x => (expR x)^-1.
  apply/funext => z.
  by rewrite expRN.
rewrite -/mu.
have /(_ _ _)/cvg_lim := @ge0_limn_integraly _ mu (fun x => expR (- x)).
move=> <-//; last 2 first.
  by move=> x; exact: expR_ge0.
  exact: measurableT_comp.
rewrite -{1}(@add0e _ 1).
apply/cvg_lim => //.
rewrite -cvg_shiftS/=.
under eq_cvg => n.
  rewrite (@continuous_FTC2 _ (fun x => expR (- x)) (fun x => - expR (- x))%R 0%R n.+1%:R)//; last 3 first.
  - rewrite expRN1.
    apply: continuous_subspaceT => x.
    apply: continuousV.
      by rewrite gt_eqF// expR_gt0.
    exact: continuous_expR.
  - have cX : continuous (fun x : R => - expR (- x))%R.
      move=> /= x; rewrite /continuous_at.
      apply: cvgN.
      rewrite expRN1.
      rewrite [X in _ --> X](_:_= (expR x)^-1)%R; last first.
        suff : (fun x => @expR R (- x)) =1 (fun x => (expR x)^-1) by [].
        by rewrite -funeqE.
      apply: cvgV.
        by rewrite gt_eqF// expR_gt0.
      exact: continuous_expR.
    split.
    + by [].
    + exact: right_continuousW.
    + exact: left_continuousW.
  - move=> x _.
    rewrite derive1E deriveN//= -derive1E.
    rewrite derive1_comp// !derive1E deriveN//.
    rewrite derive_id mulrN1 opprK.
    by rewrite -[in RHS]derive_expR.
  rewrite oppr0 expR0 -EFinB opprK.
  rewrite EFinD.
  over.
rewrite /=.
apply: (@cvgeD _ _ _ R _ _ 0%R 1%:E) => //; last exact: cvg_cst.
rewrite -(@oppeK _ 0%R).
under eq_cvg do rewrite EFinN.
apply : (@cvgeN _ _ _ _ _ (- 0%R)).
rewrite oppe0.
rewrite (@cvg_shiftS _ (fun n => (expR (1 *- n))%:E)).
apply: cvg_EFin; first exact/nearW.
exact: cvgn_expR.
Qed.

Let I_rec n : I n.+1 = n.+1%:R%:E * I n.
Proof.
(* using integration by parts *)
Admitted.

Let In n : I n = n`!%:R%:E.
Proof.
elim: n => [|n ih].
  by rewrite I0 fact0.
by rewrite I_rec ih -EFinM -natrM factS.
Qed.

Lemma Gamma_nat (n : nat) :
  Gamma n%:R = n.-1`!%:R%:E :> \bar R.
Proof.
rewrite -In /I /Gamma.
Admitted.

End Gamma.

(* not used *)
Lemma eq_set_integral {d} {T : measurableType d} {R : realType}
    {mu : measure T R} {D E : set T} (f : T -> \bar R) :
  measurable D -> measurable E ->
  measurable_fun (D `|` E) f ->
  mu (D `+` E) = 0 ->
  \int[mu]_(x in D) f x = \int[mu]_(x in E) f x.
Proof.
move=> mD mE mf.
rewrite setY_def measureU; last 3 first.
      exact: measurableD.
    exact: measurableD.
  by rewrite setIDA setDKI set0D.
move/eqP.
rewrite padde_eq0 => // => /andP[/eqP DE0 /eqP ED0].
transitivity (\int[mu]_(x in D `&` E) f x).
  rewrite -{1}(setUIDK D E).
  rewrite integralE [RHS]integralE.
  congr (_ - _).
    rewrite ge0_integral_setU//=; last 4 first.
            exact: measurableI.
          exact: measurableD.
        apply: measurable_funS (measurable_funepos mf).
          exact: measurableU.
        rewrite subUset; split; apply: subset_trans (subsetUl _).
          exact: subIsetl.
        exact: subDsetl.
      rewrite disj_set2E.
      apply/eqP.
      by rewrite -{1}(setCK E) -setDE -setDUr setvU setDT.
    rewrite [X in _ + X]null_set_integral; last 3 first.
Abort.

Lemma itv_bnd_infty_bigcup_shiftn (R : realType) b (x : R) (n : nat):
  [set` Interval (BSide b x) +oo%O] =
  \bigcup_i [set` Interval (BSide b x) (BLeft (x + (i + n.+1)%:R))].
Proof.
apply/seteqP; split=> y; rewrite /= !in_itv/= andbT; last first.
  by move=> [k _ /=]; move: b => [|] /=; rewrite in_itv/= => /andP[//] /ltW.
move=> xy; exists (`|Num.ceil (y - x)|)%N => //=.
rewrite in_itv/= xy/=.
rewrite natrD.
rewrite natr_absz.
rewrite intr_norm.
rewrite addrA.
apply: ltr_pwDr; first by rewrite (_: 0%R = 0%:R)// ltr_nat.
rewrite -lterBDl.
apply: (le_trans (le_ceil _)) => //=.
rewrite le_eqVlt; apply/predU1P; left.
apply/esym/normr_idP.
rewrite -RceilE.
apply: Rceil_ge0.
rewrite subr_ge0.
move: xy.
by case: b => //=; exact: ltW.
Qed.

Lemma itv_bnd_infty_bigcup_shiftS (R : realType) b (x : R):
  [set` Interval (BSide b x) +oo%O] =
  \bigcup_i [set` Interval (BSide b x) (BLeft (x + i.+1%:R))].
Proof.
under eq_bigcupr do rewrite -addn1.
exact: itv_bnd_infty_bigcup_shiftn.
Qed.

Import numFieldNormedType.Exports.

Section improper_integration_by_substitution.
Local Open Scope ereal_scope.
Context {R : realType}.
Notation mu := lebesgue_measure.
Implicit Types (F G f : R -> R) (a b : R).

Import set_interval real_interval.

Lemma decreasing_fun_itv_infty_bnd_bigcup F (x : R) :
  {in `[x, +oo[ &, {homo F : x y /~ (x < y)%R}} ->
  F x @[x --> +oo%R] --> -oo%R ->
  `]-oo, F x]%classic = \bigcup_i `](F (x + i.+1%:R)%R), F x]%classic.
(*  [set` Interval -oo%O (BSide b (F x))] =
  \bigcup_i [set` Interval (BLeft (F (x + i%:R)%R)) (BSide b (F x))].
*)
Proof.
move=> decrF nyF.
rewrite itv_infty_bnd_bigcup.
rewrite eqEsubset; split.
  move=> y/= [n _]/=.
  rewrite in_itv/= => /andP[Fxny yFx].
  have [i iFxn] : exists i, (F (x + i.+1%:R) < F x - n%:R)%R.
    move/cvgrNy_lt : nyF.
    move/(_ (F x - n%:R)%R) => [z [zreal zFxn]].
    exists `| Num.ceil (z - x) |%N.
    apply: zFxn.
    rewrite -ltrBlDl.
    rewrite (le_lt_trans (Num.Theory.le_ceil _))//.
      exact: num_real.
    rewrite (le_lt_trans (ler_norm _))//.
    rewrite -natr1.
    rewrite -intr_norm.
    by rewrite ltrDl.
  exists i => //=.
  rewrite in_itv/=; apply/andP; split => //.
  exact: lt_le_trans Fxny.
move=> z/= [n _ /=].
rewrite in_itv/= => /andP[Fxnz zFx].
exists `| Num.ceil (F (x + n.+1%:R)%R - F x)%R |%N.+1 => //=.
rewrite in_itv/= zFx andbT.
rewrite lerBlDr -lerBlDl.
rewrite (le_trans _ (abs_ceil_ge _))//.
rewrite ler_normr; apply/orP; right.
rewrite opprB.
apply: lerB => //.
by rewrite ltW.
Qed.

Lemma ge0_integration_by_substitution_decreasing_opinfty F G a :
  {in `[a, +oo[ &, {homo F : x y /~ (x < y)%R}} ->
  {in `]a, +oo[, continuous F^`()} ->
  cvg (F^`() x @[x --> a^'+]) ->
  cvg (F^`() x @[x --> +oo%R]) ->
  (* derivable_oo_continuous_bnd F a +oo *)
  F x @[x  --> a^'+] --> F a ->
  {in `]a, +oo[, forall x, derivable F x 1%R} ->
  {within `]-oo, F a], continuous G} ->
  (* {in `]-oo, F a[, continuous G} ->
  (G x @[x --> (F a)^'-] --> G (F a)) -> *)
  F x @[x --> +oo%R] --> -oo%R ->
  {in `]-oo, F a], forall x, (0 <= G x)%R} ->
  \int[mu]_(x in `]-oo, F a]) (G x)%:E =
  \int[mu]_(x in `[a, +oo[) (((G \o F) * - F^`()) x)%:E.
Proof.
move=> decrF cdF /cvg_ex[/= dFa cdFa] /cvg_ex[/= dFoo cdFoo].
move=> cFa dF /continuous_within_itvycP[cG cGFa] Fny G0.
have mG n : measurable_fun `](F (a + n.+1%:R)), (F a)] G.
  apply: (@measurable_fun_itv_oc _ _ _ false true).
  apply: open_continuous_measurable_fun; first exact: interval_open.
  move=> x; rewrite inE/= in_itv/= => /andP[_ xFa].
  by apply: cG; rewrite in_itv/=.
have mGFNF' i : measurable_fun `[a, (a + i.+1%:R)[ ((G \o F) * - F^`())%R.
  apply: (@measurable_fun_itv_co _ _ _ false true).
  apply: open_continuous_measurable_fun; first exact: interval_open.
  move=> x; rewrite inE/= in_itv/= => /andP[ax _].
  apply: continuousM; last first.
    apply: continuousN.
    by apply: cdF; rewrite in_itv/= andbT.
  apply: continuous_comp.
    have := derivable_within_continuous dF.
    rewrite continuous_open_subspace; last exact: interval_open.
    by apply; rewrite inE/= in_itv/= andbT.
  by apply: cG; rewrite in_itv/=; apply: decrF; rewrite ?in_itv/= ?lexx ?ltW.
transitivity (limn (fun n => \int[mu]_(x in `[F (a + n%:R)%R, F a]) (G x)%:E)).
  rewrite (decreasing_fun_itv_infty_bnd_bigcup decrF Fny).
  rewrite seqDU_bigcup_eq.
  rewrite ge0_integral_bigcup/=; first last.
  - exact: trivIset_seqDU.
  - rewrite -seqDU_bigcup_eq.
    move=> x [n _ /=]; rewrite in_itv/= => /andP[_ xFa].
    exact: G0.
  - rewrite -seqDU_bigcup_eq.
    apply/measurable_EFinP.
    exact/measurable_fun_bigcup.
  - move=> n.
    apply: measurableD => //.
    exact: bigsetU_measurable.
  apply: congr_lim.
  apply/funext => n.
  rewrite -ge0_integral_bigsetU//=; last 5 first.
  - move=> m.
    apply: measurableD => //.
    exact: bigsetU_measurable.
  - exact: iota_uniq.
  - exact: (@sub_trivIset _ _ _ [set: nat]).
  - apply/measurable_EFinP.
    rewrite big_mkord.
    rewrite -bigsetU_seqDU.
    apply: (measurable_funS _ (@bigsetU_bigcup _ (fun k =>`]F (a + k.+1%:R)%R, _]%classic) _)).
      exact: bigcup_measurable.
    exact/measurable_fun_bigcup.
  - move=> x xFaSkFa.
    apply: G0.
    have : (x \in `]-oo, F a]%classic -> x \in `]-oo, F a]) by rewrite inE.
    apply.
    rewrite (decreasing_fun_itv_infty_bnd_bigcup decrF Fny).
    apply: mem_set.
    apply: (@bigsetU_bigcup _ _ n).
    rewrite (bigsetU_seqDU (fun i => `](F (a + i.+1%:R)), (F a)]%classic)).
    by rewrite -(@big_mkord _ _ _ _ xpredT (seqDU (fun i => `](F (a + i.+1%:R)), (F a)]%classic))).
  rewrite -integral_itv_obnd_cbnd; last first.
    case: n => //.
    by rewrite addr0 set_interval.set_itvoc0; apply: measurable_fun_set0.
  congr (integral _).
  rewrite big_mkord -bigsetU_seqDU.
  rewrite -(bigcup_mkord n (fun k => `](F (a + k.+1%:R)), (F a)]%classic)).
  rewrite eqEsubset; split.
    move=> x [k /= kn].
    rewrite !in_itv/= => /andP[FaSkx ->].
    rewrite andbT.
    rewrite (le_lt_trans _ FaSkx)//.
    move: kn.
    rewrite leq_eqVlt => /predU1P[-> //|Skn].
    apply/ltW/decrF; rewrite ?in_itv/= ?andbT ?ltW ?ltrDl ?ler_ltD ?ltr_nat//.
    by rewrite ltr0n (leq_trans _ Skn).
  case: n => [|n]; first by rewrite addr0 set_interval.set_itvoc0.
  by apply: (@bigcup_sup _ _ n) => /=.
transitivity (limn (fun n => \int[mu]_(x in `]a, (a + n%:R)%R[) (((G \o F) * - F^`()) x)%:E)); last first.
  rewrite -integral_itv_obnd_cbnd; last first.
    rewrite itv_bnd_infty_bigcup_shiftS.
    apply/measurable_fun_bigcup => //.
    move=> n.
    apply: measurable_funS (mGFNF' n) => //.
    exact: subset_itv_oo_co.
  rewrite itv_bnd_infty_bigcup_shiftS.
  rewrite seqDU_bigcup_eq.
  rewrite ge0_integral_bigcup/=; last 4 first.
  - move=> n.
    apply: measurableD => //.
    exact: bigsetU_measurable.
  - rewrite -seqDU_bigcup_eq.
    apply/measurable_fun_bigcup => //.
    move=> n.
    apply/measurable_EFinP.
    apply: measurable_funS (mGFNF' n) => //.
    exact: subset_itv_oo_co.
  - move=> x ax.
    have {}ax : (a < x)%R.
      move: ax.
      rewrite -seqDU_bigcup_eq => -[? _]/=.
      by rewrite in_itv/= => /andP[].
    rewrite fctE.
    apply: mulr_ge0.
    + apply: G0.
      rewrite in_itv/= ltW//.
      by apply: decrF; rewrite ?in_itv/= ?lexx// ltW.
    + rewrite oppr_ge0.
      apply: (@decr_derive1_le0 _ _ _ `[a, +oo[).
          rewrite itv_interior.
          by move=> ?; rewrite inE/=; apply: dF.
        by move=> ? ?; rewrite !inE/=; apply: decrF.
      by rewrite itv_interior/= in_itv/= andbT.
  - exact: trivIset_seqDU.
  apply: congr_lim.
  apply/funext => n.
  rewrite -integral_bigsetU_EFin/=; last 4 first.
  - move=> k.
    apply: measurableD => //.
    exact: bigsetU_measurable.
  - exact: iota_uniq.
  - exact: (@sub_trivIset _ _ _ [set: nat]).
  - apply/measurable_EFinP.
    apply: (measurable_funS (measurable_itv `]a, (a + n.+1%:R)[)).
      rewrite big_mkord.
      rewrite -bigsetU_seqDU.
      rewrite -(bigcup_mkord _ (fun k => `]a, (a + k.+1%:R)[%classic)).
      move=> x [k /= kn].
      rewrite !in_itv/= => /andP[-> xaSk]/=.
      apply: (lt_trans xaSk).
      by rewrite ler_ltD// ltr_nat.
    apply: measurable_funS (mGFNF' n) => //.
    exact: subset_itv_oo_co.
  congr (integral _).
  rewrite big_mkord -bigsetU_seqDU.
  rewrite -(bigcup_mkord n (fun k => `]a, (a + k.+1%:R)[%classic)).
  rewrite eqEsubset; split.
    case: n; first by rewrite addr0 set_itvoo0.
    move=> n.
    by apply: (@bigcup_sup _ _ n) => /=.
  move=> x [k /= kn].
  rewrite !in_itv/= => /andP[-> xaSk]/=.
  rewrite (lt_le_trans xaSk)//.
  move: kn.
  rewrite leq_eqVlt => /orP[/eqP -> //|Skn].
  apply/ltW.
  by rewrite ler_ltD// ltr_nat.
apply: congr_lim.
apply/funext => -[|n].
  by rewrite addr0 set_itv1 integral_set1 set_itv_ge -?leNgt ?bnd_simp// integral_set0.
rewrite integration_by_substitution_decreasing.
- rewrite integral_itv_bndo_bndc// ?integral_itv_obnd_cbnd//.
  + rewrite -setUitv1; last by rewrite bnd_simp ltrDl.
    rewrite measurable_funU//; split; last exact: measurable_fun_set1.
    apply: measurable_funS (mGFNF' n) => //; exact: subset_itv_oo_co.
  + apply: measurable_funS (mGFNF' n) => //; exact: subset_itv_oo_co.
- by rewrite ltrDl.
- move=> x y /=; rewrite !in_itv/= => /andP[ax _] /andP[ay _] yx.
  by apply: decrF; rewrite //in_itv/= ?ax ?ay.
- move=> x; rewrite in_itv/= => /andP[ax _].
  by apply: cdF; rewrite in_itv/= ax.
- exact: (cvgP dFa).
- apply: (cvgP (F^`() (a + n.+1%:R))).
  apply: cvg_at_left_filter.
  apply: cdF.
  rewrite in_itv/= andbT.
  by rewrite ltr_pwDr.
- split.
  + move=> x; rewrite in_itv/= => /andP[ax _].
    by apply: dF; rewrite in_itv/= ax.
  + exact: cFa.
  + apply: cvg_at_left_filter.
    apply: differentiable_continuous.
    apply/derivable1_diffP.
    apply: dF.
    rewrite in_itv/= andbT.
    by rewrite ltr_pwDr.
- apply/continuous_within_itvP.
    apply: decrF.
    + by rewrite in_itv/= andbT lerDl.
    + by rewrite in_itv/= lexx.
    + by rewrite ltr_pwDr.
  split.
  + move=> y; rewrite in_itv/= => /andP[_ yFa].
    by apply: cG; rewrite in_itv/= yFa.
  + apply: cvg_at_right_filter.
    apply/cG.
    rewrite in_itv/=.
    apply: decrF.
    * by rewrite in_itv/= andbT lerDl.
    * by rewrite in_itv/= lexx.
    * by rewrite ltr_pwDr.
  + exact: cGFa.
Qed.

Lemma ge0_integration_by_substitution_oppr_oinfty G a :
  {in `]-oo, (- a)%R[, continuous G} ->
  (G x @[x --> (- a)%R^'-] --> G (- a)%R) ->
  cvg ((EFin \o G) x @[x --> +oo%R]) ->
  \int[mu]_(x in `]-oo, (- a)%R]) (G x)%:E =
  \int[mu]_(x in `[a, +oo[) ((G \o -%R) x)%:E.
Proof.
move=> cG GNa.
move/cvg_ex => /=[]; case.
Abort.

Lemma ge0_integration_by_substitution_oppr_oinfty_infty G a :
  {within `]-oo, (- a)%R], continuous G} ->
  (* {in `]-oo, (- a)%R[, continuous G} ->
  (G x @[x --> (- a)%R^'-] --> G (- a)%R) -> *)
  {in `]-oo, (- a)%R], forall x, (0 <= G x)%R} ->
  \int[mu]_(x in `]-oo, (- a)%R]) (G x)%:E =
  \int[mu]_(x in `[a, +oo[) ((G \o -%R) x)%:E.
Proof.
move=> /continuous_within_itvycP[cG GNa] G0.
have Dopp : (@GRing.opp R)^`() = cst (-1).
  by apply/funext => z; rewrite derive1E derive_val.
rewrite ge0_integration_by_substitution_decreasing_opinfty//; last 7 first.
- by move=> x y _ _; rewrite ltrN2.
- rewrite Dopp => ? _.
  exact: cst_continuous.
- rewrite Dopp; apply: is_cvgN; exact: is_cvg_cst.
- rewrite Dopp; apply: is_cvgN; exact: is_cvg_cst.
  apply: cvgN; exact: cvg_at_right_filter.
- by apply/continuous_within_itvycP; split.
- exact/cvgNrNy.
apply: eq_integral => x _; congr EFin.
rewrite fctE -[RHS]mulr1; congr (_ * _)%R.
rewrite -[RHS]opprK; congr -%R.
rewrite derive1E.
exact: derive_val.
Qed.

Lemma ge0_integration_by_substitution_increasing_opinfty F G a :
  {in `[a, +oo[ &, {homo F : x y / (x < y)%R}} ->
  {in `]a, +oo[, continuous F^`()} ->
  cvg (F^`() x @[x --> a^'+]) ->
  cvg (F^`() x @[x --> +oo%R]) ->
  (* derivable_oo_continuous_bnd F a +oo *)
  F x @[x  --> a^'+] --> F a ->
  {in `]a, +oo[, forall x, derivable F x 1%R} ->
  {within `[F a, +oo[, continuous G} ->
  (* {in `]F a, +oo[, continuous G} ->
  (G x @[x --> (F a)^'+] --> G (F a)) -> *)
  F x @[x --> +oo%R] --> +oo%R ->
  {in `[F a, +oo[, forall x, (0 <= G x)%R} ->
  \int[mu]_(x in `[F a, +oo[) (G x)%:E =
  \int[mu]_(x in `[a, +oo[) (((G \o F) * F^`()) x)%:E.
Proof.
move=> incrF cF' /cvg_ex[/= r F'ar] /cvg_ex[/= l F'ool] cFa dF.
move=> /continuous_within_itvcyP[cG cGFa] Fny G0.
transitivity (\int[mu]_(x in `[F a, +oo[) (((G \o -%R) \o -%R) x)%:E).
  by apply/eq_integral => x ? /=; rewrite opprK.
have cGN : {in `]-oo, - F a[%R, continuous (G \o -%R)}.
  move=> x; rewrite in_itv/= ltrNr => FaNx.
  apply: continuous_comp; first exact: continuousN.
  by apply: cG; rewrite in_itv/= FaNx.
rewrite -ge0_integration_by_substitution_oppr_oinfty_infty//; last 2 first.
- apply/continuous_within_itvycP; split => //.
  apply/cvg_at_rightNP.
  apply: cvg_toP; first by apply/cvg_ex; exists (G (F a)).
  by move/cvg_lim: cGFa => -> //; rewrite fctE opprK.
- by move=> x; rewrite in_itv/= lerNr => FaNx; apply: G0; rewrite in_itv/= FaNx.
rewrite (@ge0_integration_by_substitution_decreasing_opinfty (- F)%R); first last.
- move=> y.
  rewrite in_itv/= lerNr => FaNy.
  by apply: G0; rewrite in_itv/= FaNy.
- exact/cvgNrNy.
- apply/continuous_within_itvycP; split => //.
  rewrite fctE opprK.
  exact/cvg_at_rightNP.
- move=> x ax.
  apply: derivableN.
  exact: dF.
- exact: cvgN.
- apply/cvg_ex; exists (- l)%R.
  have := (cvgN F'ool).
  move/(_ (@filter_filter R _ proper_pinfty_nbhs)).
  apply: cvg_trans.
  apply: near_eq_cvg.
  near=> z.
  rewrite derive1E deriveN -?derive1E//.
  apply: dF; rewrite in_itv/= andbT.
  near: z.
  rewrite near_nbhs.
  apply: nbhs_pinfty_gt.
  exact: num_real.
- apply/cvg_ex; exists (- r)%R.
  have := cvgN F'ar.
  move/(_ (@filter_filter R _ (at_right_proper_filter a))).
  apply: cvg_trans.
  apply: near_eq_cvg.
  near=> z.
  rewrite derive1E deriveN -?derive1E//.
  by apply: dF; rewrite in_itv/= andbT.
- move=> x ax.
  rewrite /continuous_at.
  rewrite derive1E deriveN -?derive1E; last exact: dF.
  have := cvgN (cF' x ax).
  move/(_ (nbhs_filter x)).
  apply: cvg_trans.
  apply: near_eq_cvg.
  rewrite near_simpl/=.
  near=> z.
  rewrite derive1E deriveN -?derive1E//.
  apply: dF.
  near: z.
  rewrite near_nbhs.
  apply: (@open_in_nearW _ _ `]a, +oo[).
      exact: interval_open.
    by move=> ?; rewrite inE/=.
  by rewrite inE/=.
- move=> x y ax ay yx.
  rewrite ltrN2.
  exact: incrF.
have mGF : measurable_fun `]a, +oo[ (G \o F).
  apply: (@measurable_comp _ _ _ _ _ _ `]F a, +oo[%classic) => //.
  - move=> /= _ [x] /[!in_itv]/= /andP[ax xb] <-.
    by rewrite incrF ?incrF// in_itv/= ?lexx/= ?(ltW ab)//= ?(ltW ax) ?(ltW xb).
  - apply: open_continuous_measurable_fun; first exact: interval_open.
    by move=> x; rewrite inE/= => Fax; exact: cG.
  - apply: subspace_continuous_measurable_fun => //.
    apply: derivable_within_continuous => x.
    exact: dF.
have mF' : measurable_fun `]a, +oo[ (- F)%R^`().
  apply: open_continuous_measurable_fun; first exact: interval_open.
  move=> x; rewrite inE/= => ax.
  rewrite /continuous_at.
  rewrite derive1E deriveN; last exact: dF.
  rewrite -derive1E.
  under eq_cvg do rewrite -(opprK ((- F)%R^`() _)); apply: cvgN.
  move: (cF' x ax).
  apply: cvg_trans.
  apply: near_eq_cvg => /=.
  rewrite near_simpl.
  near=> z.
  rewrite !derive1E deriveN ?opprK//.
  apply: dF.
  near: z.
  rewrite near_nbhs.
exact: near_in_itv_oy.
rewrite -!integral_itv_obnd_cbnd; last 2 first.
- apply: measurable_funM => //.
  apply: open_continuous_measurable_fun; first exact: interval_open.
  by move=> x; rewrite inE/=; exact: cF'.
- apply: measurable_funM.
    apply: (measurable_comp (measurable_itv `]-oo, (- F a)%R[)).
        move=> _/=[x + <-].
        rewrite !in_itv/= andbT=> ax.
        rewrite ltrN2.
        by apply: incrF; rewrite ?in_itv/= ?lexx ?ltW.
      apply: open_continuous_measurable_fun; first exact: interval_open.
      by move=> x; rewrite inE/=; exact: cGN.
    apply: measurableT_comp => //.
    apply: subspace_continuous_measurable_fun => //.
    exact: derivable_within_continuous.
  exact: measurableT_comp => //.
apply: eq_integral => x/=; rewrite inE/= => ax.
congr EFin.
rewrite !fctE/= opprK; congr (_ * _)%R.
rewrite !derive1E deriveN ?opprK//.
exact: dF.
Unshelve. all: end_near. Qed.

Lemma integration_by_substitution_decreasing_opinfty_old F G a :
  {in `[a, +oo[ &, {homo F : x y /~ (x < y)%R}} ->
  {in `]a, +oo[, continuous F^`()} ->
  cvg (F^`() x @[x --> a^'+]) ->
  cvg (F^`() x @[x --> +oo%R]) ->
  (* derivable_oo_continuous_bnd F a +oo *)
  F x @[x  --> a^'+] --> F a ->
  {in `]a, +oo[, forall x, derivable F x 1%R} ->
  (* {within `]-oo, F a[, continuous G *)
  {in `]-oo, F a[, continuous G} ->
  (G x @[x --> (F a)^'-] --> G (F a)) ->
  F x @[x --> +oo%R] --> -oo%R ->
  \int[mu]_(x in `]-oo, F a]) (G x)%:E =
  \int[mu]_(x in `[a, +oo[) (((G \o F) * - F^`()) x)%:E.
Proof.
move=> decrF cdF /cvg_ex[/= dFa cdFa] /cvg_ex[/= dFoo cdFoo].
move=> cFa dF cG cGFa Fny.
transitivity (limn (fun n => \int[mu]_(x in `[F (a + n%:R)%R, F a]) (G x)%:E)).
  rewrite (decreasing_fun_itv_infty_bnd_bigcup decrF Fny).
  rewrite seqDU_bigcup_eq.
  rewrite integral_bigcup/=; last 3 first.
        exact: trivIset_seqDU.
      move=> n.
      admit.
    admit. (* ? *)
  apply: congr_lim.
  apply/funext => n.
  rewrite -integral_bigsetU_EFin//=; last 4 first.
  - admit.
  - admit.
  - admit.
  - rewrite big_mkord.
    rewrite -bigsetU_seqDU.
    apply: (measurable_funS (measurable_itv `]-oo, F a])).
      admit.
    admit.
  rewrite -integral_itv_obnd_cbnd; last first.
    admit.
  congr (integral _).
  rewrite big_mkord -bigsetU_seqDU.
  rewrite -(bigcup_mkord n (fun k => `](F (a + k.+1%:R)), (F a)]%classic)).
  rewrite eqEsubset; split.
    move=> x [k /= kn].
    rewrite !in_itv/= => /andP[FaSkx ->].
    rewrite andbT.
    rewrite (le_lt_trans _ FaSkx)//.
    move: kn.
    rewrite leq_eqVlt => /orP[/eqP -> //|Skn].
    apply/ltW; apply: decrF.
        admit.
      admit.
    by rewrite ler_ltD// ltr_nat.
  case: n; first by rewrite addr0 set_interval.set_itvoc0.
  move=> n.
  by apply: (@bigcup_sup _ _ n) => /=.
transitivity (limn (fun n => \int[mu]_(x in `[a, (a + n%:R)%R[) (((G \o F) * - F^`()) x)%:E)); last first.
  rewrite itv_bnd_infty_bigcup_shiftS.
  rewrite seqDU_bigcup_eq.
  rewrite integral_bigcup/=; last 3 first.
  - admit.
  - admit.
  - admit. (* ? *)
  apply: congr_lim.
  apply/funext => n.
  rewrite -integral_bigsetU_EFin/=; last 4 first.
  - admit.
  - admit.
  - admit.
  - admit.
  congr (integral _).
  rewrite big_mkord -bigsetU_seqDU.
  rewrite -(bigcup_mkord n (fun k => `[a, (a + k.+1%:R)[%classic)).
  rewrite eqEsubset; split.
    case: n; first by rewrite addr0 set_interval.set_itvco0.
    move=> n.
    by apply: (@bigcup_sup _ _ n) => /=.
  move=> x [k /= kn].
  rewrite !in_itv/= => /andP[-> xaSk]/=.
  rewrite (lt_le_trans xaSk)//.
  move: kn.
  rewrite leq_eqVlt => /orP[/eqP -> //|Skn].
  apply/ltW.
  by rewrite ler_ltD// ltr_nat.
apply: congr_lim.
apply/funext => -[|n].
  by rewrite addr0 set_itv1 integral_set1 set_itv_ge -?leNgt ?lexx// integral_set0.
rewrite integration_by_substitution_decreasing.
- rewrite integral_itv_bndo_bndc//.
  admit.
- by rewrite ltrDl.
- move=> x y /=; rewrite !in_itv/= => /andP[ax _] /andP[ay _] yx.
  by apply: decrF; rewrite //in_itv/= ?ax ?ay.
- move=> x; rewrite in_itv/= => /andP[ax _].
  by apply: cdF; rewrite in_itv/= ax.
- exact: (cvgP dFa).
- apply: (cvgP (F^`() (a + n.+1%:R))).
  apply: cvg_at_left_filter.
  apply: cdF.
  rewrite in_itv/= andbT.
  by rewrite ltr_pwDr.
- split.
  + move=> x; rewrite in_itv/= => /andP[ax _].
    by apply: dF; rewrite in_itv/= ax.
  + exact: cFa.
  + apply: cvg_at_left_filter.
    apply: differentiable_continuous.
    apply/derivable1_diffP.
    apply: dF.
    rewrite in_itv/= andbT.
    by rewrite ltr_pwDr.
- apply/continuous_within_itvP.
    apply: decrF.
    + by rewrite in_itv/= andbT lerDl.
    + by rewrite in_itv/= lexx.
    + by rewrite ltr_pwDr.
  split.
  + move=> y; rewrite in_itv/= => /andP[_ yFa].
    by apply: cG; rewrite in_itv/= yFa.
  + apply: cvg_at_right_filter.
    apply: cG.
    rewrite in_itv/=.
    apply: decrF.
    * by rewrite in_itv/= andbT lerDl.
    * by rewrite in_itv/= lexx.
    * by rewrite ltr_pwDr.
  + exact: cGFa.
Abort.

End improper_integration_by_substitution.

Section Rintegral_lemmas.

Context {R : realType}.
Let mu := @lebesgue_measure R.

Lemma Rintegral_even (D : set R) (f : R -> R) :
  measurable D ->
  measurable_fun D f ->
  (D = -%R @` D) ->
  {in D, f =1 f \o -%R} ->
  (\int[lebesgue_measure]_(x in D) f x =
     2 * \int[lebesgue_measure]_(x in [set x | D x /\ (0 <= x)%R]) f x)%R.
Proof.
wlog: D / ~ D 0%R.
  have ND00 : ~ (D `\ 0%R) 0%R by move=> /= [_]; exact.
  have [|] := EM (D 0%R); last first.
    have -> : D = D `\ 0%R.
(*
      rewrite eqEsubset; split => x.
        move=> Dx/=; split => //.
          move=> x0.
          apply: (ND00).
          rewrite -x0/=; split => //.
          admit.
        by rewrite /=; move/and_comm => -[].
        rewrite  -implypN.
        
        move/(_ (@Logic.eq_refl R 0%R)).
        
        move=> []; last move/eqP.
    by move=> _; exact.
    
  move/(_ (D `\ 0%R)).
  have ND00 : ~ (D `\ 0%R) 0%R by move=> /= [_]; exact.
  move/(_ ND00) => H mD mf symD evenf.
  rewrite /Rintegral.
  rewrite -(@integral_setD1_EFin _ _ 0%R); last 2 first.
      move: mD; rewrite -(@setD1K _ 0%R D).
      rewrite measurableU.

set Dp := [set x : R | D x /\ (0 < x)%R].
set Dn := [set x : R | D x /\ (x < 0)%R].
have sepD : D = Dp `|` Dn.
  rewrite eqEsubset; split => [x Dx|x].
  case : ltP x 0.*)
Abort.

Lemma ge0_integralT_even (f : R -> R) :
  (forall x, (0 <= f x)%R) ->
  continuous f ->
  f =1 f \o -%R ->
    (\int[mu]_x (f x)%:E =
     2%:E * \int[mu]_(x in [set x | (0 <= x)%R]) (f x)%:E).
Proof.
move=> f0 cf evenf.
have mf : measurable_fun [set: R] f by exact: continuous_measurable_fun.
have mposnums : measurable [set x : R | (0 <= x)%R].
  by rewrite -set_interval.set_itv_c_infty//.
rewrite -(setUv [set x : R | (0 <= x)%R]) ge0_integral_setU//= ; last 4 first.
- by apply: measurableC.
- apply/measurable_EFinP.
  by rewrite setUv.
  move=> x _.
  by rewrite lee_fin.
- exact/disj_setPCl.
rewrite mule_natl mule2n.
congr +%E.
rewrite -set_interval.set_itv_c_infty// set_interval.setCitvr.
rewrite integral_itv_bndo_bndc; last exact: measurable_funTS.
rewrite -{1}oppr0 ge0_integration_by_substitution_oppr_oinfty_infty//.
- apply: eq_integral => /= x.
  rewrite inE/= in_itv/= andbT => x0.
  congr EFin.
  by rewrite (evenf x).
- exact: continuous_subspaceT.
Qed.

End Rintegral_lemmas.

Reserved Notation "'d1 f" (at level 10, f at next level, format "''d1'  f").
Reserved Notation "'d2 f" (at level 10, f at next level, format "''d2'  f").

Section partial.
Local Open Scope ring_scope.
Context {R : realType} {T : Type}.
Variable (f : R -> T -> R).

Definition partial1 y : R -> R := (f ^~ y)^`().

End partial.
Notation "'d1 f" := (partial1 f).

Section oneDsqr.
Context {R : realType}.
Implicit Type x : R.

Definition oneDsqr x : R := 1 + x ^+ 2.

Lemma oneDsqr_gt0 x : (0 < oneDsqr x :> R)%R.
Proof. by rewrite ltr_pwDl// sqr_ge0. Qed.

Lemma oneDsqr_ge0 x : (0 <= oneDsqr x :> R)%R.
Proof. by rewrite ltW// oneDsqr_gt0. Qed.

Lemma oneDsqr_ge1 x : (1 <= oneDsqr x :> R)%R.
Proof. by rewrite lerDl sqr_ge0. Qed.

Lemma oneDsqr_neq0 x : oneDsqr x != 0%R.
Proof. by rewrite gt_eqF// oneDsqr_gt0. Qed.

Lemma oneDsqrV_le1 x : (oneDsqr\^-1 x <= 1%R)%R.
Proof. by rewrite invr_le1// ?oneDsqr_ge1 ?unitf_gt0 ?oneDsqr_gt0. Qed.

Lemma continuous_oneDsqr : continuous oneDsqr.
Proof. by move=> x; apply: cvgD; [exact: cvg_cst|exact: exprn_continuous]. Qed.

Lemma continuous_oneDsqrV : continuous (oneDsqr\^-1).
Proof.
by move=> x; apply: cvgV; [exact: oneDsqr_neq0|exact: continuous_oneDsqr].
Qed.

End oneDsqr.

#[global] Hint Extern 0 (0 < oneDsqr _)%R => solve[apply: oneDsqr_gt0] : core.
#[global] Hint Extern 0 (0 <= oneDsqr _)%R => solve[apply: oneDsqr_ge0] : core.
#[global] Hint Extern 0 (1 <= oneDsqr _)%R => solve[apply: oneDsqr_ge1] : core.
#[global] Hint Extern 0 (oneDsqr _ != 0)%R => solve[apply: oneDsqr_ge1] : core.

Lemma bounded_cst {R : realType} (k : R) T (A : set T) : [bounded k | _ in A].
Proof.
rewrite /bounded_near; near=> M.
rewrite /globally/= => y Ay.
by near: M; exact: nbhs_pinfty_ge.
Unshelve. all: end_near. Qed.

Module Leibniz.

(* without ae predicates *)
Section leibniz.
Local Open Scope ring_scope.
Context {R : realType} d {Y : measurableType d}.
Variable mu : {measure set Y -> \bar R}.
Variable f : R -> Y -> R.

Variable c : R.
Variables u v : R.
Hypothesis uc : (u < c)%R.
Hypothesis cv : (c < v)%R.
Let I : set R := `]u, v[.
Let Ic : I c.
Proof. by rewrite /I/= in_itv/= uc cv. Qed.

Variable A  : set Y.
Hypothesis mA : measurable A.
(*Hypothesis muA0 : mu A = 0.*)

Variable a : R.

(* hypo (1): t |-> f(x, t) is integrable in A *)
Hypothesis intf : forall x, I x -> mu.-integrable A (EFin \o f x).

(* hypo (2): t |-> f(x, t) is derivable in I *)
Hypothesis derf1 : forall x y, I x -> A y -> derivable (f ^~ y) x 1.

(* hypo (3): the first derivative is bounded by a non-negative function integrable on A *)
Variable G : Y -> R.
Hypothesis G_ge0 : forall y, 0 <= G y.
Hypothesis intG : mu.-integrable A (EFin \o G).
Hypothesis G_ub : forall x y, I x -> A y -> `|'d1 f y x| <= G y.

Let F x' := \int[mu]_(y in A) f x' y.

Lemma cvg_differentiation_under_integral : I a ->
  h^-1 *: (F (h + a) - F a) @[h --> 0^'] --> \int[mu]_(y in A) ('d1 f) y a.
Proof.
move=> Ia; apply/cvg_dnbhsP => t [t_neq0 t_cvg0].
suff: forall x_, (forall n : nat, x_ n != a) ->
      x_ n @[n --> \oo] --> a -> (forall n, I (x_ n)) ->
    (x_ n - a)^-1 *: (F (x_ n) - F a) @[n --> \oo] -->
      \int[mu]_(y in A) ('d1 f) y a.
  move=> suf.
  apply/cvgrPdist_le => /= r r0.
  have [rho /= rho0 arhouv] := near_in_itv Ia.
  move/cvgr_dist_lt : (t_cvg0) => /(_ _ rho0)[m _ t_cvg0'].
  near \oo => N.
  pose x k := a + t (N + k)%N.
  have x_a n : x n != a by rewrite /x addrC eq_sym -subr_eq subrr eq_sym t_neq0.
  have x_cvg_a : x n @[n --> \oo] --> a.
    apply: cvg_zero.
    rewrite [X in X @ _ --> _](_ : _ = (fun n => t (n + N)%N)); last first.
      by apply/funext => n; rewrite /x fctE addrAC subrr add0r addnC.
    by rewrite cvg_shiftn.
  have Ix n : I (x n).
    apply: arhouv => /=.
    rewrite /x opprD addrA subrr.
    apply: t_cvg0' => //=.
    rewrite (@leq_trans N) ?leq_addr//.
    by near: N; exists m.
  have := suf x x_a x_cvg_a Ix.
  move=> /cvgrPdist_le/(_ _ r0)[n _ /=] {}suf.
  near=> M.
  have /suf : (n <= M - N)%N.
    by rewrite leq_subRL; near: M; exact: nbhs_infty_ge.
  rewrite /x subnKC; last by near: M; exact: nbhs_infty_ge.
  by rewrite (addrC a) addrK.
move=> {t t_neq0 t_cvg0} x_ x_neqa x_cvga Ix_.
pose g_ n y : R := (f (x_ n) y - f a y) / (x_ n - a).
have mg_ n : measurable_fun A (fun y => (g_ n y)%:E).
  apply/measurable_EFinP/measurable_funM => //.
  apply: measurable_funB.
    by have /integrableP[/measurable_EFinP] := intf (Ix_ n).
  by have /integrableP[/measurable_EFinP] := intf Ia.
have intg_ m : mu.-integrable A (EFin \o g_ m).
  rewrite /g_ /comp/=.
  under eq_fun do rewrite EFinM.
  apply: integrableMl => //.
    under eq_fun do rewrite EFinB.
    apply: integrableB; [by []|exact:intf..].
  exact: bounded_cst.
have g_cvg_d1f y : A y -> (g_ n y)%:E @[n --> \oo] --> (('d1 f) y a)%:E.
  move=> Ay.
  rewrite /g_.
  apply/fine_cvgP; split.
    exact: nearW.
  rewrite /comp/=.
  have /cvg_ex[/= l fayl] := derf1 Ia Ay.
  have d1fyal : ('d1 f) y a = l.
    apply/cvg_lim => //.
    move: fayl; rewrite /GRing.scale/=.
    by under eq_fun do rewrite mulr1.
  have H : (forall n : nat, x_ n - a != 0) /\ x_ n - a @[n --> \oo] --> 0.
    split.
      move=> x.
      by rewrite subr_eq0.
    by apply/cvgr_sub0.
  move: fayl => /cvg_dnbhsP/(_ _ H).
  rewrite /GRing.scale/=.
  under [in X in X -> _]eq_fun do rewrite mulr1 subrK.
  move=> HH.
  suff : (f (x_ x) y - f a y) / (x_ x - a) @[x --> \oo] --> ('d1 f) y a by [].
  rewrite d1fyal.
  by under eq_fun do rewrite mulrC.
have Ag_G y n : A y -> (`|(g_ n y)%:E| <= (EFin \o G) y)%E.
  move=> Ay.
  rewrite /g_.
  have [axn|axn|<-] := ltgtP a (x_ n); last first.
  - by rewrite subrr mul0r abse0 lee_fin.
  - have x_fd1f x : x \in `](x_ n), a[ -> is_derive x 1 (f^~ y) (('d1 f) y x).
      move=> xax_n; apply: DeriveDef.
        apply: derf1 => //.
        apply: set_interval.subset_itvSoo xax_n; rewrite bnd_simp.
        + have := Ix_ n.
          by rewrite /I/= in_itv/= => /andP[/ltW].
        + have := Ia.
          by rewrite /I/= in_itv/= => /andP[_ /ltW].
      by rewrite /partial1 derive1E.
    have cf : {within `[(x_ n), a], continuous (f^~ y)}.
      have : {within I, continuous (f^~ y)}.
        apply: derivable_within_continuous => /= r Ir.
        exact: derf1.
      apply: continuous_subspaceW.
        apply: set_interval.subset_itvSoo; rewrite bnd_simp.
         + have := Ix_ n.
           by rewrite /I/= in_itv/= => /andP[].
         + have := Ia.
           by rewrite /I/= in_itv/= => /andP[_].
    have [C caxn] := @MVT _ (f^~ y) (('d1 f) y) _ _ axn x_fd1f cf.
    rewrite normr_EFin normrM distrC => ->.
    rewrite normrM -mulrA distrC normfV divff// ?normr_eq0 ?subr_eq0//.
    rewrite mulr1 lee_fin G_ub// /I/=.
    apply: set_interval.subset_itvSoo caxn; rewrite bnd_simp.
    + have := Ix_ n.
      by rewrite /I/= in_itv/= => /andP[/ltW].
    + have := Ia.
      by rewrite /I/= in_itv/= => /andP[_ /ltW].
  - have x_fd1f : (forall x, x \in `]a, (x_ n)[ -> is_derive x 1 (f^~ y) (('d1 f) y x)).
      move=> x xax_n.
      apply: DeriveDef.
        apply: derf1 => //.
        apply: set_interval.subset_itvSoo xax_n; rewrite bnd_simp.
        + have := Ia.
          by rewrite /I/= in_itv/= => /andP[/ltW].
        + have := Ix_ n.
          by rewrite /I/= in_itv/= => /andP[_ /ltW].
      by rewrite /partial1 derive1E.
    have cf : {within `[a, (x_ n)], continuous (f^~ y)}.
      have : {within I, continuous (f^~ y)}.
        apply: derivable_within_continuous => /= r Ir.
        exact: derf1.
      apply: continuous_subspaceW.
        apply: set_interval.subset_itvSoo; rewrite bnd_simp.
        + have := Ia.
          by rewrite /I/= in_itv/= => /andP[].
        + have := Ix_ n.
          by rewrite /I/= in_itv/= => /andP[_].
    have [C caxn] := @MVT _ (f^~ y) (('d1 f) y) _ _ axn x_fd1f cf.
    move=> ->.
    rewrite -mulrA divff// ?subr_eq0// mulr1 lee_fin G_ub// /I/=.
    apply: set_interval.subset_itvSoo caxn; rewrite bnd_simp.
    + move: Ia.
      by rewrite /I/= in_itv/= => /andP[/ltW + _].
    + have := Ix_ n.
      by rewrite /I/= in_itv/= => /andP[_ /ltW].
have mdf : measurable_fun A (fun y => (('d1 f) y a)%:E).
  by apply: emeasurable_fun_cvg g_cvg_d1f => m; exact: mg_.
have [intd1f g_d1f_0 _] := @dominated_convergence _ _ _ mu _ mA
  (fun n y => (g_ n y)%:E) _ (EFin \o G) mg_ mdf (aeW _ g_cvg_d1f) intG (aeW _ Ag_G).
rewrite /= in g_d1f_0.
rewrite [X in X @ _ --> _](_ : _ = (fun h => \int[mu]_(z in A) g_ h z)); last first.
  apply/funext => m.
  rewrite /F -RintegralB; [|by []|exact: intf..].
  rewrite -[LHS]RintegralZl; [|by []|].
  - by apply: eq_Rintegral => y _; rewrite mulrC.
  - rewrite /comp; under eq_fun do rewrite EFinB.
    by apply: integrableB => //; exact: intf.
apply/cvgr_sub0.
rewrite (_ : (fun x => \int[mu]_(z in  A) g_ x z - \int[mu]_(y in  A) ('d1 f y a)) =
             (fun x => \int[mu]_(z in  A) (g_ x z - ('d1 f) z a)))%R; last first.
  by apply/funext => n; rewrite RintegralB.
apply: norm_cvg0.
have {}g_d1f_0 : (\int[mu]_(x in A) (normr (g_ n x - ('d1 f) x a))) @[n --> \oo] --> 0.
  exact/fine_cvg.
apply: (@squeeze_cvgr _ _ _ _ (cst 0) _ _ _ _ _ g_d1f_0) => //.
- apply/nearW => n.
  rewrite /= normr_ge0/= le_normr_integral//.
  rewrite /comp; under eq_fun do rewrite EFinB.
  by apply: integrableB => //; exact: intg_.
- exact: cvg_cst.
Unshelve. all: end_near. Qed.

Lemma differentiation_under_integral : I a ->
  F^`() a = \int[mu]_(y in A) ('d1 f y) a.
Proof.
move=> Ia.
rewrite /derive1.
have /cvg_lim-> //:= cvg_differentiation_under_integral Ia.
Qed.

Lemma derivable_under_integral : I a -> derivable F a 1.
Proof.
move=> Ia.
apply/cvg_ex => /=; exists (\int[mu]_(y in A) ('d1 f y) a).
rewrite /GRing.scale/=.
under eq_fun do rewrite mulr1.
exact: cvg_differentiation_under_integral.
Qed.

End leibniz.

Section application_to_gauss_integral.
Local Open Scope ring_scope.
Context {R : realType}.
Let mu := @lebesgue_measure R.
Definition f x := \int[mu]_(t in `[0, x]) (expR (- t ^+ 2)).
Definition g x :=
  \int[mu]_(t in `[0, 1]) (expR (- x ^+ 2 * oneDsqr t) / oneDsqr t).

Definition u (x : R) t := (expR (- x ^+ 2 * oneDsqr t) / oneDsqr t).

Let f_ge0 x : 0 <= f x.
Proof. by apply: Rintegral_ge0 => //= r _; rewrite expR_ge0. Qed.

Lemma du x t :
  ('d1 u t) x = - 2 * x * expR (- x ^+ 2) * expR (- (t * x) ^+ 2).
Proof.
rewrite /partial1.
rewrite /u /=.
rewrite derive1E.
rewrite deriveMr//=.
rewrite -derive1E.
rewrite derive1_comp//.
rewrite [in X in _ * (_ * X)]derive1E.
rewrite deriveMr//=.
rewrite mulrCA (mulrA (oneDsqr _)^-1) mulVf ?oneDsqr_neq0 ?mul1r//.
rewrite deriveN// exp_derive expr1 mulrC !mulNr; congr -%R.
rewrite -mulrA; congr *%R.
  by rewrite /GRing.scale/= mulr1.
rewrite -expRD /oneDsqr mulrDr mulr1 exprMn opprD mulrC.
rewrite derive1E.
by rewrite -[in RHS]derive_expR.
Qed.

Lemma cexp (x : R) : continuous (fun r : R => - (r * x) ^+ 2).
Proof.
move=> z; apply: cvgN => /=.
apply: (@cvg_comp _ _ _ (fun z => z * x) (fun z => z ^+ 2)).
  by apply: cvgMl; exact: cvg_id.
exact: exprn_continuous.
Qed.

Lemma cexpR (x : R) : continuous (fun r : R => expR (- (r * x) ^+ 2)).
Proof.
move=> x0.
apply: (@continuous_comp _ _ _ (fun r : R => - (r * x) ^+ 2) expR).
  exact: cexp.
exact: continuous_expR.
Qed.

Lemma cu z : continuous (u z).
Proof.
rewrite /u /= => x.
rewrite /continuous_at.
apply: cvgM; last exact: continuous_oneDsqrV.
apply: continuous_comp => /=; last exact: continuous_expR.
by apply: cvgMr; exact: continuous_oneDsqr.
Qed.

Lemma dg0 x : h^-1 *: (g (h + x)%E - g x) @[h --> 0^'] -->
  - 2 * x * expR (- x ^+ 2) * \int[mu]_(t in `[0, 1]) expR (- (t * x) ^+ 2).
Proof.
have [c [e e0 cex]] : exists c : R, exists2 e : R, 0 < e & ball c e x.
  exists x, 1 => //.
  exact: ballxx.
have [M M0 HM]: exists2 M : R, 0 < M & forall x0 y, x0 \in `](c - e), (c + e)[ ->
    y \in `[0, 1] -> normr (('d1 u) y x0) <= M.
  rewrite /=.
  near (pinfty_nbhs R) => M.
  exists M => // {x cex}x t.
  rewrite in_itv/= => /andP[cex xce].
  rewrite in_itv/= => /andP[t0 t1].
  rewrite du !mulNr normrN -!mulrA normrM ger0_norm//.
  rewrite -expRD exprMn_comm; last by rewrite /GRing.comm mulrC.
  rewrite -opprD.
  rewrite -{1}(mul1r (x ^+ 2)) -mulrDl.
  rewrite (@le_trans _ _ (2 * normr (x * expR (- x ^+ 2))))//.
    rewrite ler_pM2l// normrM [leRHS]normrM.
    rewrite ler_wpM2l//.
    do 2 rewrite ger0_norm ?expR_ge0//.
    by rewrite ler_expR// lerN2 ler_peMl ?sqr_ge0// lerDl sqr_ge0.
  rewrite normrM (ger0_norm (expR_ge0 _)).
  have ? : normr x <= maxr (normr (c + e)%E) (normr (c - e)).
    rewrite le_max.
    have [x0|x0] := lerP 0 x.
      by rewrite ger0_norm// ler_normr (ltW xce).
    rewrite ltr0_norm//; apply/orP; right.
    move/ltW : cex.
    rewrite -lerN2 => /le_trans; apply.
    by rewrite -normrN ler_norm.
  rewrite (@le_trans _ _ (2 * ((maxr `|c + e| `|c - e|) * expR (- (0) ^+ 2))))//.
    rewrite ler_pM2l// ler_pM ?expR_ge0//.
    rewrite ler_expR lerN2//.
    rewrite (_ : x ^+ 2= `|x| ^+ 2); last first.
      by rewrite real_normK// num_real.
    by rewrite ler_pXn2r ?nnegrE//.
  near: M.
  apply: nbhs_pinfty_ge.
  by rewrite num_real.
rewrite [X in _ --> X](_ : _ = \int[mu]_(y in `[0, 1]) ('d1 u) y x)//; last first.
  rewrite /= -RintegralZl//; last first.
    apply: continuous_compact_integrable => /=.
      exact: segment_compact.
    apply/continuous_subspaceT => x0.
    exact: cexpR.
  by apply: eq_Rintegral => z z01; rewrite du//.
have /= := @cvg_differentiation_under_integral R _ _ mu u _ _ `[0, 1] _ x _ _ _ _ _ HM.
apply => //=.
- move=> z z01; apply: continuous_compact_integrable => //; first exact: segment_compact.
  by apply: continuous_subspaceT; exact: cu.
- by move=> _; exact: ltW.
- apply: continuous_compact_integrable => //; first exact: segment_compact.
  by apply: continuous_subspaceT; exact: cst_continuous.
- by rewrite ball_itv/= in cex.
Unshelve. all: end_near. Qed.

Lemma derivable_g x : derivable g x 1.
Proof.
apply/cvg_ex.
eexists.
rewrite /g/=.
rewrite /GRing.scale/=.
under eq_fun.
  move=> x0.
  under eq_Rintegral do rewrite mulr1.
  over.
exact: dg0.
Qed.

Lemma dg x : g^`() x =
  - 2 * x * expR (- x ^+ 2) * \int[mu]_(t in `[0, 1]) expR (- (t * x) ^+ 2).
Proof.
apply/cvg_lim => //=.
exact: dg0.
Qed.

Lemma df x : 0 < x ->
  derivable f x 1 /\ f^`() x = expR (- x ^+ 2).
Proof.
move=> x0.
have H : continuous (fun t : R => expR (- t ^+ 2)).
  move=> x1.
  apply: (@continuous_comp _ _ _ (fun x1 : R => - x1 ^+ 2) expR).
    apply: cvgN.
    apply: (@cvg_comp _ _ _ (fun z => z) (fun z => z ^+ 2)).
      exact: cvg_id.
    exact: exprn_continuous.
  exact: continuous_expR.
rewrite /f.
apply: (@continuous_FTC1 R (fun t => expR (- t ^+ 2)) (BLeft 0) _ (x + 1) _ _ _ _).
- by rewrite ltrDl.
- apply: continuous_compact_integrable => //; first exact: segment_compact.
  exact: continuous_subspaceT.
- by rewrite /=; rewrite lte_fin.
- by move=> x1; exact: H.
Qed.

Definition h x := g x + (f x) ^+ 2.

Lemma dh x : 0 < x -> h^`() x = 0.
Proof.
move=> x0.
rewrite /h derive1E deriveD//=; last 2 first.
  exact: derivable_g.
  apply/diff_derivable.
  apply: (@differentiable_comp _ _ _ _ f (fun x => x ^+ 2)).
    apply/derivable1_diffP.
    by have [] := df x0.
  apply/derivable1_diffP.
  exact: exprn_derivable.
rewrite -derive1E dg.
rewrite -derive1E (@derive1_comp _ f (fun z => z ^+ 2))//; last first.
  by have [] := df x0.
rewrite derive1E exp_derive.
rewrite (df _).2//.
rewrite expr1 /GRing.scale/= mulr1.
rewrite addrC !mulNr; apply/eqP; rewrite subr_eq0; apply/eqP.
rewrite -!mulrA; congr *%R.
rewrite [LHS]mulrC.
rewrite [RHS]mulrCA; congr *%R.
rewrite /f [in LHS]/Rintegral.
have derM : ( *%R^~ x)^`() = cst x.
  apply/funext => z.
  rewrite derive1E.
  by rewrite deriveMr// derive_id mulr1.
have := @integration_by_substitution_increasing R (fun t => t * x) (fun t => expR (- t ^+ 2)) 0 1 ltr01.
rewrite -/mu mul0r mul1r => ->//=; last 6 first.
  move=> a b; rewrite !in_itv/= => /andP[a0 a1] /andP[b0 b1] ab.
  by rewrite ltr_pM2r//.
  rewrite derM.
  by move=> z _; exact: cvg_cst.
  by rewrite derM; exact: is_cvg_cst.
  by rewrite derM; exact: is_cvg_cst.
  split => //.
  apply: cvg_at_right_filter.
  apply: cvgM => //.
  exact: cvg_cst.
  apply: cvg_at_left_filter.
  apply: cvgM => //.
  exact: cvg_cst.
  apply: continuous_subspaceT => z.
  apply: (@continuous_comp _ _ _ (fun x : R => - x ^+ 2) expR).
    apply: continuousN.
    exact: exprn_continuous.
  exact: continuous_expR.
rewrite derM.
under eq_integral do rewrite fctE/= EFinM.
have ? :  lebesgue_measure.-integrable `[0, 1]
    (fun x1 : g_sigma_algebraType (R.-ocitv.-measurable) => (expR (- (x1 * x) ^+ 2))%:E).
  apply: continuous_compact_integrable => //.
    exact: segment_compact.
  apply: continuous_subspaceT => z.
  apply: (@continuous_comp _ _ _ (fun x1 : R => - (x1 * x) ^+ 2) expR).
    apply: continuousN.
    apply: (@continuous_comp _ _ _ (fun x1 : R => (x1 * x)) (fun x => x ^+ 2)) => //.
      by apply: cvgMl.
    exact: exprn_continuous.
  exact: continuous_expR.
rewrite integralZr//=.
rewrite fineM//=; last first.
  by apply: integral_fune_fin_num => //=.
by rewrite mulrC.
Qed.

Lemma derivable_atan (x : R) : derivable atan x 1.
Proof. exact: ex_derive. Qed.

Lemma h0 : h 0 = pi / 4.
Proof.
rewrite /h /f set_itv1 Rintegral_set1 expr0n addr0.
rewrite -atan1.
rewrite /g.
under eq_Rintegral do rewrite expr0n/= oppr0 mul0r expR0 mul1r.
rewrite /Rintegral.
rewrite (@continuous_FTC2 _ _ atan)//.
- by rewrite atan0 sube0.
- by apply: continuous_in_subspaceT => x ?; exact: continuous_oneDsqrV.
- split.
  + by move=> x _; exact: derivable_atan.
  + by apply: cvg_at_right_filter; exact: continuous_atan.
  + by apply: cvg_at_left_filter; exact: continuous_atan.
- move=> x x01.
  by rewrite derive1_atan// mul1r.
Qed.

Lemma encadrement0 t (x : R) : t \in `[0, 1] ->
  0 <= expR (- x ^+ 2 * oneDsqr t) / oneDsqr t <= expR (- x ^+ 2).
Proof.
move=> t01.
apply/andP; split.
  by rewrite divr_ge0 ?expR_ge0// oneDsqr_ge0.
rewrite ler_pdivrMr ?oneDsqr_gt0 //.
rewrite (@le_trans _ _ (expR (- x ^+ 2)))//.
  by rewrite ler_expR// mulNr lerN2 ler_peMr// ?sqr_ge0 ?oneDsqr_ge1.
by rewrite ler_peMr// ?expR_ge0 ?oneDsqr_ge1.
Qed.

Lemma encadrement x : 0 <= g x <= expR (- x ^+ 2).
Proof.
rewrite /g; apply/andP; split.
  rewrite /Rintegral fine_ge0// integral_ge0//= => t t01.
  by rewrite lee_fin divr_ge0 ?expR_ge0// oneDsqr_ge0.
have -> : expR (- x ^+ 2) = \int[mu]_(t in `[0, 1]) expR (- x ^+ 2).
  rewrite /Rintegral integral_cst//. (* TODO: lemma Rintegral_cst *)
  by rewrite /mu/= lebesgue_measure_itv//= lte01 oppr0 adde0 mule1/=.
rewrite fine_le//.
- apply: integral_fune_fin_num => //=.
  apply: continuous_compact_integrable.
    exact: segment_compact.
  apply: continuous_in_subspaceT => y y01.
  apply: cvgM.
    apply: continuous_comp => //=.
      move=> z.
      by apply: cvgMr; exact: continuous_oneDsqr.
    exact: continuous_expR.
  exact: continuous_oneDsqrV.
- apply: integral_fune_fin_num => //=.
  apply: continuous_compact_integrable.
    exact: segment_compact.
  apply: continuous_subspaceT => z.
  exact: cvg_cst.
apply: ge0_le_integral => //=.
- by move=> y _; rewrite lee_fin divr_ge0 ?expR_ge0// oneDsqr_ge0.
- apply/measurable_EFinP => /=.
  apply: measurable_funM => //=.
    apply: measurableT_comp => //=.
    apply: measurable_funM => //=.
    exact: measurable_funD.
  apply: measurable_funTS.
  by apply: continuous_measurable_fun; exact: continuous_oneDsqrV.
- by by move=> y _; rewrite lee_fin expR_ge0.
- move=> y y01.
  rewrite lee_fin.
  by have /andP[] := encadrement0 x y01.
Qed.

Lemma cvg_g : g x @[x --> +oo] --> 0.
Proof.
apply: (@squeeze_cvgr _ _ _ _ (cst 0) (fun x => expR (- x ^+ 2))); last 2 first.
  exact: cvg_cst.
  apply: (@cvg_comp _ _ _ (fun x => x ^+ 2) (fun x => expR (- x))); last first.
    exact: cvgr_expR.
  (* TODO: lemma *)
  apply/cvgryPge => M.
  near=> x.
  rewrite (@le_trans _ _ x)//.
    near: x.
    apply: nbhs_pinfty_ge => //.
    by rewrite num_real.
  by rewrite expr2 ler_peMl.
near=> n => /=.
exact: encadrement.
Unshelve. all: end_near. Qed.

Lemma cvg_f : (f x) ^+ 2 @[x --> +oo] --> pi / 4.
Proof.
have H1 x : 0 < x -> h x = h 0.
  move=> x0.
  have [] := @MVT _ h h^`() 0 x x0.
  - move=> r; rewrite in_itv/= => /andP[r0 rx].
    apply: DeriveDef.
    apply: derivableD => /=.
      exact: derivable_g.
    under eq_fun do rewrite expr2//=.
    by apply: derivableM; have [] := df r0.
    by rewrite derive1E.
  - have cf : {within `[0, x], continuous f}.
      rewrite /f.
      apply: parameterized_integral_continuous => //=.
      apply: continuous_compact_integrable => //.
        exact: segment_compact.
      apply: continuous_subspaceT => z.
      apply: (@continuous_comp _ _ _ (fun x1 : R => - (x1) ^+ 2) expR).
        apply: continuousN.
        exact: exprn_continuous.
      exact: continuous_expR.
    rewrite /h.
    move=> z.
    apply: continuousD; last first.
      red.
      rewrite /continuous_at.
      rewrite expr2.
      under [X in X @ _ --> _]eq_fun do rewrite expr2.
      apply: cvgM.
        exact: cf.
      exact: cf.
    apply: derivable_within_continuous => u u0x.
    exact: derivable_g.
  move=> c.
  rewrite in_itv/= => /andP[c0 cx].
  by rewrite dh// mul0r => /eqP; rewrite subr_eq0 => /eqP.
have H2 x : 0 < x -> (f x) ^+ 2 = pi / 4 - g x.
  move/H1/eqP; rewrite {1}/h eq_sym addrC -subr_eq => /eqP/esym.
  by rewrite h0.
suff: pi / 4 - g x @[x --> +oo] --> pi / 4.
  apply: cvg_trans.
  apply: near_eq_cvg.
  near=> x.
  by rewrite H2.
rewrite -[in X in _ --> X](subr0 (pi / 4)).
apply: cvgB => //.
  exact: cvg_cst.
exact: cvg_g.
Unshelve. end_near. Qed.

Lemma gauss : \int[mu]_(t in `[0, +oo[) (expR (- t ^+ 2)) = Num.sqrt pi / 2.
Proof.
have cvg_f : f x @[x --> +oo] --> Num.sqrt pi / 2.
  have : Num.sqrt (f x ^+ 2) @[x --> +oo] --> Num.sqrt (pi / 4).
    apply: continuous_cvg => //.
      exact: sqrt_continuous.
    exact: cvg_f.
  rewrite sqrtrM ?pi_ge0// sqrtrV// (_ : 4 = 2 ^+ 2); last first.
    by rewrite expr2 -natrM.
  rewrite sqrtr_sqr ger0_norm//.
  rewrite (_ : (fun x => Num.sqrt (f x ^+ 2)) = f)//.
  by apply/funext => r; rewrite sqrtr_sqr// ger0_norm.
rewrite /f in cvg_f.
rewrite /Rintegral.
have /(_ _ _)/cvg_lim := @ge0_limn_integraly _ mu (fun x => expR (- x ^+ 2)).
move=> <-//; last 2 first.
  by move=> x; exact: expR_ge0.
  apply: measurableT_comp => //.
  by apply: measurableT_comp => //.
suff: (limn (fun n : nat => (\int[mu]_(x in `[0%R, n%:R]) (expR (- x ^+ 2))%:E)%E)) = (Num.sqrt pi / 2)%:E.
  move=> suf.
  by rewrite suf//.
apply/cvg_lim => //.
have H : (n%:R : R) @[n --> \oo] --> +oo.
  (* TODO: lemma? *)
  apply/cvgryPge => M.
  exact: nbhs_infty_ger.
move/cvg_pinftyP : cvg_f => /(_ _ H).
move/neq0_fine_cvgP; apply.
by rewrite gt_eqF// divr_gt0// sqrtr_gt0 pi_gt0.
Qed.

End application_to_gauss_integral.

End Leibniz.

Section leibniz.
Local Open Scope ring_scope.
Context {R : realType} d {Y : measurableType d}.
Variable mu : {measure set Y -> \bar R}.
Variable A : set R.
Hypothesis openA : open A.
Variable f : R -> Y -> R.
Variable theta : Y -> R.
Variable B : set Y.
Hypothesis mB : measurable B.

Hypothesis inttheta : mu.-integrable B (EFin \o theta).

Hypothesis intf : forall x, A x -> mu.-integrable B (EFin \o (f x)).
Hypothesis derf1 :
  (*{ae mu,*) forall y, B y -> forall x, A x -> derivable (f ^~ y) x 1(*}*).
Hypothesis theta_ge0 : forall y : Y, 0 <= theta y.

Variable a : R.

Hypothesis theta_ub :
  forall x, A x -> forall y, `|'d1 f y x| <= theta y.
(* ref: https://planetmath.org/differentiationundertheintegralsign *)

Let F x' := \int[mu]_(y in B) f x' y.

(* ref: https://www.math.wustl.edu/~sk/math4121.02-12-2021.pdf *)
Lemma differentiation_under_integral : A a ->
  F^`() a = \int[mu]_(y in B) ('d1 f y) a.
Proof.
move=> Aa.
have [e e0 xeA] : exists2 e, (0 < e) & `](a - e), (a + e)[ `<=` A.
  rewrite /=.
  have [r r0 H] := open_itvoo_subset openA Aa.
  exists (r / 2) => //.
    by rewrite divr_gt0.
  apply: H; last by rewrite divr_gt0.
  rewrite /ball_/= sub0r normrN gtr0_norm ?divr_gt0//.
  by rewrite ltr_pdivrMr// ltr_pMr// ltr1n.
have H1 : (forall x0 : R, `](a - e), (a + e)%E[%classic x0 -> mu.-integrable B (EFin \o f x0)).
  move=> r xer.
  apply: intf.
  by apply: xeA.
have H2 : (forall (x0 : R) (y : Y), `](a - e), (a + e)%E[%classic x0 -> B y -> derivable (f^~ y) x0 1) .
  move=> r y xer N1y.
  apply: derf1 => //.
  exact: xeA.
have H4 : (forall (x0 : R) (y : Y),
    `](a - e), (a + e)%E[%classic x0 -> (B) y -> normr (('d1 f) y x0) <= theta y).
  move=> r y xer N1y.
  apply: theta_ub.
  by apply: xeA.
have := @Leibniz.differentiation_under_integral R _ Y mu f (a - e) (a + e) B mB a H1 H2 theta theta_ge0 inttheta H4.
move=> H.
rewrite /F.
rewrite H//.
rewrite -ball_itv.
exact: ballxx.
Qed.

End leibniz.

Section thm227a.
Local Open Scope ring_scope.
Context {R : realType}.
Let mu := @lebesgue_measure R.

(* folland thm2.27(a) *)
(* additional ref: https://laurent.claessens-donadello.eu/pdf/lefrido.pdf *)
Lemma continuous_under_integral (f : R -> R -> R) (g : R -> R) (x0 : R) :
  (forall x, mu.-integrable setT (EFin \o (f x))) ->
  (forall y, {for x0, continuous (f ^~ y)}) ->
  mu.-integrable setT (EFin \o g) ->
  (forall x y, `|f x y| <= g y) ->
  let F x := (\int[mu]_(y in setT) f x y)%R in
  {for x0, continuous F}.
Proof.
move=> intf cf intg domfg F.
have [x_ [x0xn cvgx0]] : exists x_ : nat -> R, (forall n, x0 < x_ n) /\ x_ n @[n --> \oo] --> x0.
  admit.
set f_ := fun (n : nat) (y : R) => f (x_ n) y.
have : forall y, f_ n y @[n --> \oo] --> f x0 y.
  move=> y.
  apply: (cvg_dnbhsP (f ^~ y) x0 (f x0 y)).1; last first.
    split.
      move=> n.
      by rewrite gt_eqF.
    exact: cvgx0.
  apply/cvgrPdist_le.
  move=> e e0.
  near=> x.
  move: (cf y).
  move/cvgrPdist_le => /=.
  move/(_ e e0).
rewrite /prop_near1.
rewrite /nbhs/=.
rewrite /nbhs_ball_ /filter_from/=.
move=> [].
move=> r r0/=.
move/(_ x0).
rewrite /ball_.
  admit.
Abort.

Lemma continuous_integral (mx Mx my My : R) (f : R -> R -> R) :
  (forall x, mu.-integrable `[my, My] (EFin \o (f x))) ->
  (exists g : R -> R, mu.-integrable `[my, My] (EFin \o g) /\
      {in `[mx, Mx], forall x : R,
         {in `[my, My], forall y, (`|(f x y)| <= g y)%R}}) ->
  {in `]mx, Mx[, forall x0 : R,
      {in `]my, My[, forall y, continuous_at x0 (f ^~ y)}} ->
  let F x := (\int[mu]_(y in `[my, My]) f x y)%R in
    {in `]mx, Mx[, continuous F}.
Proof.
move=> intfx.
move=> [domi [intdomi fdomi]].
move=> cfy.
move=> F.
move=> x; rewrite in_itv/= => /andP[mxx xMx].
rewrite /continuous_at.
(* apply/cvg_dnbhsP. *)
Abort.
(*
have : exists x_ : nat -> R, (forall n, x_ n \in `]mx, Mx[) /\ x_ n @[n --> \oo] --> x.
  admit.
move=> [x_ [x_itv x_x]].
have := (@dominated_convergence _ _ _ mu `]my, My[ _
   (fun n => (fun y => (f (x_ n) y)%:E)) (EFin\o (f x)) (EFin \o domi)).
xxx
*)

End thm227a.

Section Gauss_integration.
Context {R : realType}.

(* TODO: PR *)
Lemma locally_integrable_cst (x : R) :
  locally_integrable setT (cst x).
Proof.
split.
- exact: measurable_cst.
- exact: openT.
- move=> K _ cK.
  under eq_integral.
    move=> z zK/=.
    rewrite (_:(normr x)%:E = cst (normr x)%:E z); last by [].
    over.
  rewrite integral_cst/=; last exact: compact_measurable.
  apply: lte_mul_pinfty => //.
  exact: compact_finite_measure.
Qed.

Local Import Num.

(* for lemmas only for integral yet *)
Let EFinK (x : R) : x = fine (EFin x).
Proof. by []. Qed.

Definition gauss := (fun x : R => expR (- (x ^+ 2)))%R.

Let gauss_ge0 (x : R) : (0 <= gauss x)%R. Proof. by exact: expR_ge0. Qed.

(* related to expR (- (x ^+ 2)) is rapidly decreasing function *)
Let measurable_gauss : measurable_fun (@setT R) gauss.
Proof.
apply: measurableT_comp => //.
exact: measurableT_comp.
Qed.

Let mu := @lebesgue_measure R.
Let Ig := (\int[mu]_(x in `[0%R, +oo[) gauss x)%R.

Let Ig_fin_num : (\int[mu]_(x in `[0%R, +oo[) (gauss x)%:E) \is a fin_num.
Proof.
rewrite ge0_fin_numE//; last by apply: integral_ge0 => ? _; rewrite lee_fin.
rewrite (_: `[0%R, +oo[%classic = `[0%R, 1%R[ `|` `[1%R, +oo[); last first.
  by apply: set_interval.itv_bndbnd_setU; rewrite bnd_simp.
rewrite ge0_integral_setU => //; last 3 first.
- apply: measurable_funTS.
  exact: measurableT_comp.
- by move=> ? _; apply: gauss_ge0.
- apply: set_interval.lt_disjoint.
  move=> x y; rewrite !in_itv/= => /andP[_ x1] /andP[y1 _].
  exact: lt_le_trans x1 y1.
apply: lte_add_pinfty.
  apply: (@le_lt_trans _ _ (\int[mu]_(x in `[0%R, 1%R[) (fun=> 1%:E) x)).
    apply: ge0_le_integral => //; last 2 first.
        by apply: measurable_funTS; apply: measurableT_comp.
      move=> x _; rewrite lee_fin -expR0.
      by rewrite ler_expR lerNl oppr0 sqr_ge0.
    by move=> ? _; rewrite lee_fin.
  rewrite integral_cst/=; last exact: measurable_itv.
  by rewrite lebesgue_measure_itv/= lte01 oppr0 adde0 mule1 ltey.
apply: (@le_lt_trans _ _ (\int[mu]_(x in `[1%R, +oo[) (expR (- x))%:E)).
  apply: ge0_le_integral => //=; last 4 first.
          by apply: measurable_funTS; apply: measurableT_comp.
        by move=> ? _; apply: expR_ge0.
      apply: measurable_funTS.
      apply: measurableT_comp => //.
      exact: measurableT_comp.
    move=> x.
    rewrite in_itv/= => /andP[x1 _].
    rewrite lee_fin ler_expR lerN2 expr2.
    rewrite ler_peMl//.
    exact: le_trans x1.
  by move=> x _; rewrite lee_fin.
apply: (@le_lt_trans _ _ (\int[mu]_(x in `[0%R, +oo[) (expR (- x))%:E)).
  apply: ge0_subset_integral => //=.
      apply: measurable_funTS.
      apply: measurableT_comp => //.
      exact: measurableT_comp.
    by move=> x _; rewrite lee_fin; exact: expR_ge0.
  by apply: set_interval.subset_itvr; rewrite bnd_simp.
have cvgr_NexpR : -%R (@expR R (- x)) @[x --> +oo%R] --> 0%R.
  rewrite -oppr0.
  apply: cvgN.
  exact: cvgr_expR.
rewrite (ge0_within_pinfty_continuous_FTC2 _ cvgr_NexpR); last 5 first.
- by move=> x x0; rewrite expR_ge0.
- apply/continuous_within_itvcyP; split.
    move=> ? _; apply: continuous_comp.
      exact: continuousN.
    exact: continuous_expR.
  apply: cvg_at_right_filter.
  rewrite expRN.
  under eq_cvg do rewrite expRN.
  apply: cvgV; first by rewrite expR0.
  exact: continuous_expR.
- move=> x x0.
  apply/derivable1_diffP.
  apply: differentiable_comp => //=.
  apply: differentiable_comp => //=.
  apply/derivable1_diffP.
  exact: derivable_expR.
- apply: cvg_at_right_filter.
  apply: cvgN => //.
  rewrite expRN.
  under eq_cvg do rewrite expRN.
  apply: cvgV; first by rewrite expR0.
  exact: continuous_expR.
- move=> x x0.
  rewrite derive1_comp => //.
  rewrite derive1E.
  rewrite deriveN => //=.
  rewrite (@derive_val _ _ _ _ _ _ _ (is_derive_id (expR (- x)) 1%R)).
  rewrite (_:(fun x => expR (- x)) = expR \o -%R) => //.
  rewrite derive1_comp => //.
  rewrite !derive1E.
  have /funeqP -> := derive_expR R.
  rewrite mulrCA -[RHS]mulr1; congr (_ * _)%R.
  rewrite (@derive_val _ _ _ _ _ _ _ (is_deriveNid x 1%R)).
  by rewrite mulN1r opprK.
by rewrite sub0e oppr0 expR0 EFinN oppeK ltey.
Qed.

Let zeroE : 0%R = @GRing.natmul R 1%R 0%N.
Proof. by []. Qed.
Let oneE : 1%R = @GRing.natmul R 1%R 1%N.
Proof. by []. Qed.

(* for lower bound of  *)
Let pi2n := fun n => ((@pi R) / 2 - n.+1%:R^-1)%:E.

Let incr_pi2n :
 {homo pi2n : n m / (n <= m)%N >-> n <= m}.
Proof.
apply/nondecreasing_seqP => n.
rewrite lee_fin.
apply: lerB => //.
by rewrite ler_pV2; rewrite ?ler_nat// inE// unitfE lt0r_neq0/=.
Qed.

Let itv_pinftyE : [set x : R| True /\ (0 <= x)%R] = `[0%R, +oo[%classic.
Proof. by rewrite eqEsubset; split => x//=; rewrite andB in_itv/= andbT. Qed.

(* NB: not used *)
(*Let even_oneDsqrx (x : R) : oneDsqr x = oneDsqr (- x).
Proof. by rewrite /oneDsqr; congr +%R; rewrite !expr2 mulrN mulNr opprK. Qed.*)

Let dJ (x y : R) := (expR ((- x ^+ 2)%R * oneDsqr y) / oneDsqr y)%R.

Let J (x : R) := (\int[mu]_(y in `[0%R, +oo[) (dJ x y))%R.

Let fin_num_int_V1sqrx n : \int[@lebesgue_measure R]_(x in `[0%R, n%:R]) (oneDsqr\^-1 x)%:E \is a fin_num.
Proof.
have int1_lty : \int[@lebesgue_measure R]_(_ in `[0%R, n%:R]) 1 < +oo.
  rewrite integral_cst//= mul1e lebesgue_measure_itv.
  by case: ifP => //= _; rewrite oppr0 adde0 ltey.
rewrite ge0_fin_numE; last first.
  by apply: integral_ge0 => x _; rewrite lee_fin invr_ge0 oneDsqr_ge0.
apply: le_lt_trans int1_lty.
apply: ge0_le_integral => //=.
- by move=> x _; rewrite lee_fin invr_ge0 oneDsqr_ge0.
- apply: measurableT_comp => //; apply: measurable_funTS.
  apply: continuous_measurable_fun => //.
  exact: continuous_oneDsqrV.
- by move=> x _; rewrite lee_fin; move: (oneDsqrV_le1 x).
Qed.

Let datan : {in `]0%R, +oo[, (@atan R)^`() =1 oneDsqr\^-1}.
Proof.
move=> x _.
rewrite derive1E.
exact: derive_val.
Qed.

Let J0E :
 \int[mu]_(y in `[0%R, +oo[) (dJ 0%R y)%:E = (@pi R / 2)%:E.
Proof.
rewrite /dJ expr0n/= oppr0.
under eq_integral do rewrite mul0r expR0 div1r.
rewrite (ge0_within_pinfty_continuous_FTC2 _ (@cvgy_atan R))/=; last 5 first.
- by move=> x _; rewrite invr_ge0 oneDsqr_ge0.
- apply/continuous_within_itvcyP; split.
    by move=> x x0; apply: continuous_oneDsqrV.
  by apply: cvg_at_right_filter; apply: continuous_oneDsqrV.
- move=> x x0; apply: ex_derive.
- by apply: cvg_at_right_filter; apply: continuous_atan.
- by move=> x _; rewrite derive1E; apply: derive_val.
by rewrite atan0 oppr0 addr0.
Qed.

(*
apply/esym/cvg_lim => //.
under eq_cvg => x.
  rewrite (EFinK (atan x)) -(subr0 (atan x)) -atan0 EFinB.
  rewrite -(within_continuous_FTC2 ge0_VoneDsqrx'); last 5 first.
  - apply: cvg_EFin.
      apply: nearW => z; by rewrite fin_numElt ltNyr ltey.
    exact: continuous_atan.

rewrite itvaybig; under eq_bigcupr do rewrite add0r.
rewrite (EFinK (pi / 2)%R); congr (fine _).
rewrite -ge0_nondecreasing_set_cvg_integral//; last 4 first.
- apply/nondecreasing_seqP => n.
            rewrite subsetEset.
            by apply: set_interval.subset_itvl; rewrite bnd_simp ler_nat.
          exact: bigcup_measurable.
        apply: measurable_funTS.
        apply: measurableT_comp => //.
        exact: continuous_measurable_fun.
      move=> x _.
      rewrite lee_fin.
      rewrite invr_ge0 => //.
      apply: addr_ge0 => //.
      exact: sqr_ge0.
    apply/eqP; rewrite eq_le; apply/andP; split.
      apply: ub_ereal_sup => r/= [n _ <-].
      case: n.
        rewrite set_interval.set_itv1 integral_set1 lee_fin.
        by apply: divr_ge0 => //; apply: pi_ge0.
      move=> n.
      rewrite (@within_continuous_FTC2 _ _ atan)//; last 3 first.
            apply: continuous_subspaceT.
            move=> x/=.
            apply: cvgV.
              apply: lt0r_neq0.
              apply: ltr_pwDl => //.
              exact: sqr_ge0.
            apply: cvgD => //=; first exact: cvg_cst.
            exact: sqr_continuous.
          split => /=.
              move=> x _.
              exact: ex_derive.
            apply: cvg_at_right_filter.
            exact: continuous_atan.
          apply: cvg_at_left_filter.
          exact: continuous_atan.
        move=> x _.
        rewrite derive1E.
        exact: derive_val.
      by rewrite atan0 sube0 lee_fin ltW// atan_ltpi2.
(*    have esup_pi2 : ereal_sup [set (@pi R / 2 - n.+1%:R^-1)%:E | n in [set: Datatypes.nat]] = (pi / 2)%:E.
      have /cvg_lim <- // := (ereal_nondecreasing_cvgn incr_pi2n).
      apply/cvg_lim => //.
      apply: cvg_EFin.
        near=> n.
        rewrite ge0_fin_numE; last first.
          rewrite lee_fin.
          rewrite subr_ge0.
          apply: le_trans (pihalf_ge1 R).
          rewrite invf_le1 => //.
          by rewrite oneE ler_nat.
        by rewrite EFinB lteBlDl// addey// ltey.
      rewrite -{2}(subr0 (pi / 2)%R).
      apply: cvgB; first exact: cvg_cst.
      rewrite (_: 0%R = inf [set x.+1%:R^-1 | x in [set: Datatypes.nat]]); last first.
        apply/esym/eqP; rewrite eq_le; apply/andP; split.
          have half_lt1 : (normr (@GRing.inv R 2%:R) < 1)%R.
            by rewrite ger0_norm// invf_lt1// {1}oneE ltr_nat.
          have /cvg_lim <- // := (@cvg_geometric R (2%:R^-1) (2%:R^-1) half_lt1).
          have := @nonincreasing_cvgn R (geometric 2^-1 2^-1)%R.
          have ninc_geo : {homo geometric (@GRing.inv R 2) 2^-1 :
                            n m / (n <= m)%N >-> (m <= n)%R}.
            apply/nonincreasing_seqP => n/=.
            apply: ler_wpM2l => //.
            apply: ler_wiXn2l => //.
            rewrite invr_le1; first by rewrite {1}oneE// ler_nat.
              apply: unitf_gt0; rewrite {1}zeroE// ler_nat.
            by rewrite {1}zeroE// ler_nat.
          have lb_rgeo : has_lbound (range (geometric (@GRing.inv R 2) 2^-1)).
            exists 0%R => _ [n _ <-].
            rewrite /= -exprS.
            exact: exprn_ge0.
          move/(_ ninc_geo).
          move/(_ lb_rgeo).
          move/cvg_lim => ->//.
          apply: le_inf; last 2 first.
              exists 2^-1; exists 0%N => //=.
              by rewrite expr0 mulr1.
            split.
              by exists 1%R; exists 0%N => //; rewrite invr1.
            exists 0%R => _ [n _ <-].
            by rewrite invr_ge0 zeroE ler_nat.
          move=> _ [_ [n _ <-] <-].
          exists (- 2^-1 ^+ n.+1)%R; split.
            exists (2^-1 ^+ n.+1)%R => //; first exists ((2 ^ n.+1).-1) => //.
            rewrite prednK; last exact: expn_gt0.
            by rewrite natrX exprVn.
          by rewrite lerN2 exprS.
        apply: lb_le_inf.
          by exists 1%R; exists 0%N => //; rewrite invr1.
        move=> _ [n _ <-].
        by rewrite invr_ge0 zeroE ler_nat.
      apply: nonincreasing_cvgn.
        apply/nonincreasing_seqP => n.
        by rewrite lef_pV2 ?ler_nat// posrE.
      exists 0%R => _ [n _ <-].
      by rewrite invr_ge0 zeroE ler_nat.
    rewrite -esup_pi2. *) 
    rewrite [leLHS](_:_= ereal_sup [set (atan r)%:E | r in [set: R]]); last first.
      have nondecreasing_EFin_atan: {homo (fun x => (@atan R x)%:E) : n m / (n <= m)%R >-> n <= m}.
        by move=> x y xy; rewrite lee_fin; apply: nondecreasing_atan.
      have /cvg_lim <- // := nondecreasing_cvge nondecreasing_EFin_atan.
      apply/esym/cvg_lim => //.
      apply: cvg_EFin.
        near=> x.
        rewrite ge0_fin_numE; first exact: ltey.
        by rewrite lee_fin -atan0 nondecreasing_atan.
      rewrite fctE/=.
      exact: atan_pinfty_pi2.
    rewrite [X in ereal_sup X <= _](_:_= [set z%:E | z in range atan]); last first.
      rewrite eqEsubset; split.
        by move=> _ [x _ <-]; exists (atan x) => //; exists x.
      by move=> _ [_ [x _ <-] <-]; exists x.
    rewrite [X in _ <= ereal_sup X](_:_ =
        [set z%:E | z in range (fun n =>
          (fine (\int[lebesgue_measure]_(x in `[0%R, n%:R]) (oneDsqrx\^-1 x)%:E)))]); last first.
      rewrite eqEsubset; split.
        move=> _ [n _ <-].
        exists (\int[lebesgue_measure]_(x in `[0%R, n%:R]) (oneDsqrx\^-1 x))%R => //.
        by rewrite fineK.
      move=> _ [_ [n _ <-] <-].
      exists n => //.
      rewrite fineK//.
    rewrite !ereal_sup_EFin; last 4 first.
    - 
admit.
    - admit.
    - admit.
    - admit.
    apply: le_sup; last 2 first.
    - by exists (atan 0); exists 0%R.
    - split.
      + admit.
      * admit.
    move=> _ [x _ <-].
    case : (leP x 0%R) => [x0|x0].
      exists 0%R; split.
        by exists 0%R => //; rewrite set_interval.set_itv1 integral_set1.
      rewrite -atan0.
      by apply: nondecreasing_atan.
    exists (atan (Rceil x)); split; last first.
      apply: nondecreasing_atan.
      exact: Rceil_ge.
    have := ltW x0.
    move/ge0_Rceil_nat => [].
    case.
      move=> cx0.
      suff : ~ (0 < x)%R by rewrite x0.
      apply/negP; rewrite -leNgt.
      by rewrite zeroE cx0 Rceil_ge.
    move=> n xn.
    exists n.+1 => //=.
    have datan0Sn : {in `]0%R, n.+1%:R[, (@atan R)^`() =1 (fun x => 1 / (1%R + (x ^+ 2)%R)%E)}.
      move=> z; rewrite in_itv/= => /andP[z0 _].
      by apply: datan; rewrite in_itv/= z0.
    under eq_integral do rewrite -div1r.
    rewrite (within_continuous_FTC2 _ _ _ datan0Sn); last 3 first.
    - by rewrite zeroE ltr_nat.
    - apply: continuous_subspaceT.
      by under [X in continuous X]eq_fun do rewrite div1r.
    - split.
      + move=> z _.
        exact: ex_derive.
      + apply: cvg_at_right_filter.
        exact: continuous_atan.
      + apply: cvg_at_left_filter.
        exact: continuous_atan.
    by rewrite atan0 sube0 xn.
Unshelve. end_near. Admitted.
(*
rewrite /J.
under eq_Rintegral do rewrite expr0n/= mul0r oppr0 expR0.
(* need Rintegral version of ge0_within_pinfty_continuous_FTC2 *)
rewrite (EFinK (pi / 2)); congr (fine _).
rewrite (ge0_within_pinfty_continuous_FTC2 _ J0 _ _ _ datan); last 4 first.
- move=> x x0.
  apply: divr_ge0 => //.
  rewrite addr_ge0//.
  apply: exprn_ge0.
  exact: ltW.
- rewrite div1r.
  apply/cvgVP => //.
  rewrite invrK.
  under eq_cvg do rewrite /=div1r invrK.
  apply: cvgD; first exact: cvg_cst.
  rewrite expr2.
  under eq_cvg do rewrite expr2.
  by apply: cvgM; apply: cvg_at_right_filter; apply: cvg_id.
- move=> x x0.
  apply/cvgVP.
    by rewrite div1r invr_neq0// lt0r_neq0// addr_gt0// exprn_gt0.
  under eq_cvg do rewrite /=div1r invrK.
  rewrite div1r invrK.
  apply: cvgD; first exact: cvg_cst.
  rewrite expr2.
  under eq_cvg do rewrite expr2.
  by apply: cvgM; apply: cvg_id.
- move=> x x0.
  under eq_fun do rewrite div1r.
  by apply: derivableV; rewrite //lt0r_neq0// addr_gt0// exprn_gt0.
- rewrite atan0 sube0.
  move: J0; move/cvg_lim => <- //.
  apply/cvg_lim => //.
  apply: cvg_EFin.
    exact: nearW.
  exact: atan_pinfty_pi2.
Qed.
*)
*)

Let atan_cvg_to_J0 : (atan x)%:E @[x --> +oo%R] --> (J 0)%:E.
Proof.
rewrite fineK J0E//.
apply: cvg_EFin; last exact: cvgy_atan.
near=> x.
rewrite ge0_fin_numE; last first. by rewrite lee_fin -atan0 le_atan.
apply: (@lt_trans _ _ (pi / 2)%:E); last exact: ltey.
by rewrite lte_fin atan_ltpi2.
Unshelve. end_near. Qed.

Let mdJ x : measurable_fun setT (EFin \o (dJ x)).
Proof.
apply: measurableT_comp => //.
rewrite /dJ -mulrfctE.
apply: measurable_funM.
  apply: measurableT_comp => //.
  apply: measurableT_comp => //.
  apply: measurableT_comp => //.
  exact: measurable_funD.
apply: continuous_measurable_fun => //.
exact: continuous_oneDsqrV.
Qed.

Let int_J x : mu.-integrable `[0%R, +oo[ (EFin \o dJ x).
Proof.
apply/integrableP; split; first exact: measurable_funTS (mdJ x).
apply/abse_integralP => //; first exact: measurable_funTS (mdJ x).
rewrite -fin_num_abs ge0_fin_numE; last first.
  apply: integral_ge0 => z z0.
  rewrite lee_fin divr_ge0//; first exact: expR_ge0.
  apply: addr_ge0 => //.
  exact: sqr_ge0.
apply: (@le_lt_trans _ _ (\int[mu]_(y in `[0%R, +oo[) (EFin \o dJ 0%R) y)).
  apply: ge0_le_integral => //.
  - move=> z _.
    by rewrite lee_fin divr_ge0 ?expR_ge0// oneDsqr_ge0.
  - exact: measurable_funTS (mdJ x).
  - move=> z _.
    by rewrite /dJ expr0n oppr0/= mul0r expR0 div1r lee_fin invr_ge0 oneDsqr_ge0.
  - exact: measurable_funTS (mdJ 0%R).
  move=> z z0.
  rewrite lee_fin ler_pdivrMr ?oneDsqr_gt0//.
  rewrite divfK ?oneDsqr_neq0//.
  rewrite ler_expR expr0n oppr0/= mul0r pmulr_lle0 ?oneDsqr_gt0//.
  by rewrite lerNl oppr0 sqr_ge0.
by rewrite J0E ltey.
Qed.

Let Joo : J x @[x --> +oo%R] --> 0%R.
Proof.
apply/cvgrPdist_le => /= e e0.
near=> x.
rewrite sub0r ler0_norm ?opprK; last first.
  rewrite oppr_le0.
  apply: Rintegral_ge0.
  move=> y y0.
  apply: divr_ge0; first exact: expR_ge0.
  apply: addr_ge0 => //.
  exact: sqr_ge0.
apply: (@le_trans _ _ (expR (- x ^+ 2) * J 0%R)%R).
  rewrite [X in (_ <= X * _)%R]EFinK.
  rewrite -fineM//; last by rewrite J0E.
  rewrite -integralZl//; last exact: int_J.
  apply: fine_le.
  - move: (int_J x).
    (* lemma? *)
    have J_ge0 : 0%R <=
      \int[mu]_(x0 in `[0%R, +oo[) (dJ x x0)%:E.
      apply: integral_ge0 => y _.
      by rewrite lee_fin divr_ge0 ?oneDsqr_ge0// expR_ge0.
    move/integrableP => [_].
    rewrite ge0_fin_numE => //.
    move/(abse_integralP mu (measurable_itv _) (measurable_funTS (mdJ _))).
    by rewrite -(@ge0_fin_numE _ (`| _|))// abse_fin_num ge0_fin_numE/=.
  - rewrite integralZl//; last exact: int_J.
    apply: fin_numM => //.
    by rewrite J0E.
  apply: le_integral => //; first exact: int_J.
    by rewrite integrableZl//; exact: int_J.
  move=> y _.
  rewrite lee_fin ler_pdivrMr ?oneDsqr_gt0//.
  rewrite mulrA divfK ?oneDsqr_neq0//.
  rewrite expr0n oppr0/= mul0r expR0 mulr1 ler_expR.
  by rewrite ler_neMr ?oneDsqr_ge1// oppr_le0; exact: sqr_ge0.
rewrite (EFinK (expR _)) -fineM// J0E// -EFinM/=.
rewrite -ler_pdivlMr; last exact: lt_le_trans (pihalf_ge1 _).
rewrite expRN -[leRHS]invrK lef_pV2 ?posrE; last 2 first.
- exact: expR_gt0.
- by rewrite invr_gt0 divr_gt0//; apply: lt_le_trans (pihalf_ge1 _).
rewrite -[leLHS]lnK ?posrE; last first.
  by rewrite invr_gt0 divr_gt0//; apply: lt_le_trans (pihalf_ge1 _).
rewrite ler_expR -ler_sqrt; last exact: sqr_ge0.
by rewrite sqrtr_sqr ger0_norm.
Unshelve. end_near. Qed.

Lemma ge0_integrable_comp_continuous_increasing (f g : R -> R)
 (l : R) (ir : itv_bound R) :
  let i := Interval (BLeft l) ir in
  {within [set` i], continuous f} ->
  {in [set` i], {homo f : x y / (x < y)%R}} ->
  {in [set` i], forall x, (0 <= g x)%R} ->
  mu.-integrable [set` i] (EFin \o g) ->
  mu.-integrable [set` i] (EFin \o (g \o f)).
Proof.
Abort.

Import Num.Theory.

Let dJE : {in `]0%R, +oo[, J^`() =1 (fun x => (- 2) * Ig * (gauss x))%R}.
Proof.
move=> x; rewrite in_itv/= => /andP[x0 _].
pose d_dx_dJ x0 y0 : R := (dJ^~ y0)^`() x0.
rewrite /J.
(* interchange integration and derivation *)
(* by lebesgue differentiaton theorem? *)
(* FTC1 *)
transitivity ((\int[mu]_(y in `[0, +oo[) d_dx_dJ x y)%R).
  pose NdJ_dx (x y : R) : R := -%R (fun y => (dJ^~ y)^`() x) y.
  pose I : set R := ball x x.
  have openI : open I.
    by apply: ball_open.
  have c : R := x / 2.
  rewrite (@differentiation_under_integral R _ _ (@lebesgue_measure R) _ openI dJ
      (fun y => (Num.sqrt (expR 1))^-1 * expR (- c ^+ 2 * y ^+ 2)))%R; last 7 first.
    by [].
    rewrite /=.
    move: Ig_fin_num.
    rewrite /gauss.
    admit. (* integrable *)
    move=> x1 /= Ix1.
    rewrite /dJ.
    admit. (* integrable *)
    move=> y/=; rewrite in_itv/= andbT => y0 r _.
    rewrite /dJ.
    admit. (* derivable *)
    move=> /= y.
    by rewrite mulr_ge0// expR_ge0.
    move=> x' Ix' /= y.
    have d1tmp : 'd1 dJ y x' = (oneDsqr y * - 2 * x' * dJ x' y)%R.
      rewrite /partial1 /dJ/=.
      rewrite (@derive1_comp _ (fun z => - z ^+ 2)%R
                (fun z => expR (z * oneDsqr y) / oneDsqr y))//=.
      rewrite !derive1E deriveN// exp_derive//= expr1.
      rewrite deriveMr//=.
      rewrite -derive1E derive1_comp//=.
      rewrite !derive1E/=.
      rewrite deriveMr//= derive_id mulr1.
      admit.
    rewrite {}d1tmp {}/dJ/=.
    rewrite [leLHS](_ : _ = 2 * normr x' * (expR (- x' ^+ 2 * oneDsqr y)))%R; last first.
      admit.
    rewrite /oneDsqr.
    rewrite mulrDr mulr1.
    rewrite expRD.
    rewrite mulrA.
    rewrite ler_pM//.
    by rewrite mulr_ge0// expR_ge0.
    by rewrite expR_ge0.
    admit.
    rewrite ler_expR// !mulNr lerN2 ler_wpM2r// ?sqr_ge0//.
    rewrite /I /ball/= in Ix'.
    admit.
    rewrite /I.
    exact/ballxx.
  done.
(*  apply: eq_Rintegral => x1; rewrite inE/= in_itv/= andbT => x10.
  rewrite /dJ /partial1/=.
  rewrite (@derive1_comp _ (fun x => - x ^+ 2)%R
            (fun y => expR (y * oneDsqrx x1) / oneDsqrx x1))//.
  rewrite !derive1E.
  rewrite deriveMr//=.
  rewrite deriveN//=.
  rewrite exp_derive//= expr1.
  rewrite -derive1E derive1_comp//=.
  rewrite !derive1E.
  rewrite deriveMr//=.
  rewrite (mulrCA _ (oneDsqrx x1)).
  rewrite !mulrA.
  rewrite mulVf// ?mul1r; last first.
    by rewrite gt_eqF// ltr_pwDl// sqr_ge0.
  rewrite derive_id mulr1.
  rewrite /d_dx_dJ /dJ.
  rewrite (@derive1_comp _ (fun x => - x ^+ 2)%R
            (fun y => expR (y * oneDsqrx x1) / oneDsqrx x1))//.
  rewrite !derive1E.
  rewrite deriveN//= exp_derive expr1.
  rewrite deriveMr//=.
  rewrite -[in RHS]derive1E derive1_comp//=.
  rewrite ![in RHS]derive1E.
  rewrite deriveMr//= derive_id mulr1.
  rewrite (mulrCA _ _ (oneDsqrx x1)).
  rewrite mulVf ?mulr1; last first.
    by rewrite gt_eqF// ltr_pwDl// sqr_ge0.
  done.*)
have substE : \int[mu]_(y in `[0%R, +oo[) (expR (- x ^+ 2 * oneDsqr y))%:E =
  \int[mu]_(y in `[0%R, +oo[)
                    ((((fun z => expR (- x ^+ 2) / x * expR (- z ^+ 2)) \o
                    (fun z => x * z)) * (fun z => x * z)^`()) y)%:E.
  apply: eq_integral => y _.
  rewrite !fctE derive1E.
  rewrite derive_val /GRing.scale/= mulr1.
  rewrite mulrAC divfK//; last by rewrite gt_eqF.
  by rewrite mulrDr mulr1 mulNr -exprMn expRD.
have int_substE : \int[mu]_(y in `[0%R, +oo[) (expR (- x ^+ 2 * oneDsqr y))%:E
 = (\int[lebesgue_measure]_(x1 in `[0%R, +oo[)
         (expR (- x ^+ 2) / x * expR (- x1 ^+ 2))%:E).
  rewrite substE.
  rewrite -ge0_integration_by_substitution_increasing_opinfty; first last.
  - move=> y _.
    apply: mulr_ge0; last exact: expR_ge0.
    apply: divr_ge0; first exact: expR_ge0.
    exact: ltW.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  by rewrite mulr0.
have mexpRVxexpR (D : set R) : measurable_fun D (fun y => (expR (- x ^+ 2) / x * expR (- y ^+ 2))%R).
  move=> mD.
  apply: measurable_funM => //.
  apply: measurableT_comp => //.
  exact: measurableT_comp.
transitivity (-2 * x * \int[mu]_(y in `[0, +oo[) (expR ((- x ^+ 2) * oneDsqr y)))%R.
  rewrite /Rintegral (_:-2 * x = fine (-2 * x)%:E)%R//.
  rewrite -fineM; last 2 first.
  - rewrite le0_fin_numE ?ltNyr//.
    rewrite lee_fin.
    by rewrite mulr_le0_ge0// ltW.
  - rewrite ge0_fin_numE; last first.
      apply: integral_ge0 => ? _.
      exact: expR_ge0.
    rewrite int_substE.
    rewrite -integral_itv_obnd_cbnd; last exact: mexpRVxexpR.
    rewrite (@itv_bndbnd_setU _ _ _ (BLeft 1%R))//; last by rewrite bnd_simp.
    rewrite ge0_integral_setU//=; first last.
    - apply: lt_disjoint => a b; rewrite !in_itv/= => /andP[_ a1] /andP[b1 _].
      exact: lt_le_trans a1 b1.
    - move=> /= z z0.
      have {}z0 : (0 < z)%R.
        by case : z0; rewrite in_itv/= => /andP[+ _]//; apply: lt_le_trans.
      rewrite lee_fin mulr_ge0//.
        by rewrite divr_ge0// ?expR_ge0// ltW.
      exact: expR_ge0.
    - apply/measurable_EFinP.
      rewrite -itv_bndbnd_setU//; last by rewrite bnd_simp.
      exact: mexpRVxexpR.
    under eq_integral do rewrite EFinM.
    rewrite ge0_integralZl//; first last.
    - by rewrite lee_fin divr_ge0// ?expR_ge0// ltW.
    - by move=> ? _; exact: expR_ge0.
    - apply/measurable_EFinP.
      by apply: measurableT_comp => //; apply: measurableT_comp.
    apply: lte_add_pinfty; last first.
      apply: (@le_lt_trans _ _ (\int[lebesgue_measure]_(x1 in `]0%R, +oo[) (expR (- x ^+ 2) / x * expR (- x1 ^+ 2))%:E)).
        apply: ge0_subset_integral => //=; first last.
        - by apply: subset_itvr; rewrite bnd_simp.
        - move=> z; rewrite in_itv/= => /andP[z0 _].
          by rewrite lee_fin mulr_ge0// ?divr_ge0// ?expR_ge0// ltW.
        apply/measurable_EFinP.
        exact: mexpRVxexpR.
      rewrite integral_itv_obnd_cbnd; last exact: mexpRVxexpR.
      under eq_integral do rewrite EFinM//.
      rewrite integralZl//; last first.
        apply/integrableP; split.
          apply/measurable_EFinP.
          apply: measurableT_comp => //.
          exact: measurableT_comp.
        apply/abse_integralP => //.
          apply/measurable_EFinP.
          by apply: measurableT_comp => //; apply: measurableT_comp.
        rewrite -ge0_fin_numE; last exact: abse_ge0.
        by rewrite abse_fin_num.
      rewrite muleC lte_mul_pinfty//.
        by apply: integral_ge0 => ? _; exact: expR_ge0.
      exact: ltey.
    apply: lte_mul_pinfty.
    - by rewrite lee_fin divr_ge0// ?expR_ge0// ltW.
    - by rewrite fin_numElt ltry ltNyr.
    apply: (@le_lt_trans _ _ Ig%:E).
      rewrite /= fineK//.
      apply: ge0_subset_integral => //; first last.
          by move=> r/=; rewrite !in_itv/= andbT => /andP[+ _]; exact: ltW.
        by move=> ? _; exact: expR_ge0.
      apply/measurable_EFinP.
      apply: measurableT_comp => //.
      exact: measurableT_comp.
    exact: ltry.
  rewrite mulNr EFinN mulNe.
  rewrite -ge0_integralZl//; first last.
  - by rewrite lee_fin mulr_ge0// ltW.
  - by move=> ? _; rewrite lee_fin expR_ge0.
  - apply/measurable_EFinP.
    apply: measurableT_comp => //.
    apply: measurable_funM => //.
    exact: measurable_funD.
  rewrite -integral_ge0N; last first.
    move=> ? _; apply: mulr_ge0; last exact: expR_ge0.
    by rewrite mulr_ge0// ltW.
  congr fine.
  apply: eq_integral=> y; rewrite inE/= in_itv/= => y0.
  rewrite /d_dx_dJ derive1E.
  rewrite /dJ; under eq_fun do (rewrite mulrC); rewrite deriveZ/=; last exact: ex_derive.
  rewrite -derive1E derive1_comp => //.
  rewrite derive1E derive_val.
  rewrite mulrC /GRing.scale/= mulrA.
  under eq_fun do (rewrite mulrC); rewrite derive1E deriveZ/=; last exact: ex_derive.
  rewrite mulrA mulVf ?mul1r ?oneDsqr_neq0//.
  rewrite deriveN// mulNr; congr (- _%:E).
  rewrite exp_derive expr1.
  by rewrite /GRing.scale/= mulr1.
rewrite /Rintegral int_substE.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl//=; first last.
- rewrite lee_fin.
  apply: divr_ge0; last exact: ltW.
  exact: expR_ge0.
- by move=> ? _; rewrite lee_fin expR_ge0.
- apply/measurable_EFinP.
  apply: measurableT_comp => //.
  exact: measurableT_comp => //.
rewrite fineM/=; first last.
- exact: Ig_fin_num.
- rewrite ge0_fin_numE; last by rewrite lee_fin divr_ge0 ?expR_ge0 ?ltW.
  exact: ltey.
rewrite -!mulrA.
rewrite [X in (-2 * X)%R]mulrCA !mulrA mulfK; last first.
  by rewrite gt_eqF.
by rewrite mulrAC.
Admitted.

(*Lemma dableJ :{in `[0%R, 1%R], forall x, derivable J x 1}.
Proof.
move=> x; rewrite in_itv/= => /andP[x0 x1].
apply/cvg_ex => /=.
exists (\int[mu]_(y in `[0%R, +oo[) ((dJ ^~ y)^`() x))%R.
under eq_cvg.
  move=> h.
  rewrite -RintegralB//.
  under eq_Rintegral.
    move=> y.
    rewrite inE/= in_itv/= => y0.
    have := @MVT _ (dJ ^~ y) (dJ ^~ y)^`() x (h + a)%R.
*)

Let rcJ0 : J x @[x --> 0^'+] --> J 0.
Proof.
apply/cvg_at_rightP.
move=> x_ [x_ge0 x_0].
rewrite /J.
have mitv : @measurable _ R `[0%R, +oo[.
  exact: measurable_itv.
have mdJx_ n : measurable_fun `[@GRing.zero R, +oo[ (fun y : R => (dJ (x_ n) y)%:E).
  by move/integrableP : (int_J (x_ n)) => [].
have mdJ0 : measurable_fun `[@GRing.zero R, +oo[ (EFin \o dJ 0).
  by move/integrableP : (int_J 0%R) => [].
have cvg_dJ : {ae mu, forall x : R, `[0%R, +oo[%classic x ->
          (dJ (x_ x0) x)%:E @[x0 --> \oo] --> (EFin \o dJ 0) x}.
  apply: aeW => /= y _.
  apply: cvg_EFin.
    apply: nearW => n.
    rewrite ge0_fin_numE; first exact: ltry.
    by rewrite lee_fin mulr_ge0// ?expR_ge0// invr_ge0// oneDsqr_ge0.
  apply: (cvg_dnbhsP (dJ ^~ y) 0%R (dJ 0 y)).1; last first.
    split.
      by move=> n; rewrite gt_eqF.
    exact: x_0.
  (* lemma *)
  apply/cvgrPdist_lep.
  near=> e.
  near=> t.
  rewrite -mulNr -mulrDl expr0n/= oppr0 mul0r expR0.
  have /normr_idP -> : (0 <= (1 - expR (- t ^+ 2 * oneDsqr y)) / oneDsqr y)%R.
    rewrite divr_ge0 ?oneDsqr_ge0//.
    rewrite subr_ge0 -expR0 ler_expR.
    by rewrite mulNr oppr_le0 mulr_ge0// ?sqr_ge0 ?oneDsqr_ge0.
  rewrite ler_pdivrMr ?oneDsqr_gt0//.
  rewrite lerBlDl -lerBlDr.
  rewrite -[leLHS]lnK; last first.
    rewrite posrE.
    rewrite subr_gt0.
    rewrite -ltr_pdivlMr ?oneDsqr_gt0//.
    near: e.
    apply: nbhs_right_lt.
    by rewrite divr_gt0// oneDsqr_gt0.
  rewrite ler_expR.
  rewrite -ler_pdivrMr ?oneDsqr_gt0//.
  rewrite lerNr.
  rewrite -ler_sqrt; last first.
    rewrite lerNr oppr0.
    rewrite mulr_le0_ge0 ?invr_ge0 ?oneDsqr_ge0//.
    apply: ln_le0.
    by rewrite gerBl mulr_ge0// oneDsqr_ge0.
  rewrite sqrtr_sqr.
  near: t.
  rewrite near_nbhs.
  apply: dnbhs0_le.
  rewrite sqrtr_gt0 oppr_gt0 pmulr_llt0 ?invr_gt0 ?oneDsqr_gt0//.
  apply: ln_lt0; apply/andP; split.
    rewrite subr_gt0 -ltr_pdivlMr ?oneDsqr_gt0//.
    near: e.
    apply: nbhs_right_lt.
    by rewrite divr_gt0// oneDsqr_gt0.
  by rewrite gtrBl mulr_gt0// oneDsqr_gt0.
have int_J0 : mu.-integrable `[0%R, +oo[ (EFin \o dJ 0) by [].
have domdJ : {ae mu, forall (x : R) (n : Datatypes.nat),
   `[0%R, +oo[%classic x -> `|(dJ (x_ n) x)%:E| <= (EFin \o dJ 0) x}.
  apply: aeW => /= x n _.
  have /normr_idP -> : (0 <= (dJ (x_ n) x))%R.
    by rewrite mulr_ge0// ?expR_ge0 ?invr_ge0 ?oneDsqr_ge0.
  rewrite lee_fin.
  apply: ler_pM => //; rewrite ?expR_ge0 ?invr_ge0 ?oneDsqr_ge0//.
  rewrite expr0n oppr0 mul0r ler_expR mulNr oppr_le0.
  by rewrite mulr_ge0 ?sqr_ge0// oneDsqr_ge0.
have /= := @dominated_convergence _ (measurableTypeR R) _ mu _ mitv _ _ _ mdJx_ mdJ0 cvg_dJ int_J0 domdJ.
move=> [_ lim_norm0 cvgJ].
apply: fine_cvg; rewrite fineK.
apply: cvgJ.
rewrite J0E ge0_fin_numE; first by rewrite ltry.
by rewrite lee_fin divr_ge0// pi_ge0.
Unshelve. all: end_near. Qed.

(*
apply: cvg_at_right_filter.
rewrite /J/Rintegral.
rewrite J0E.
apply/cvgrPdist_le => /= e e0.
rewrite near_simpl/=.
near=> x.
apply: (@le_trans _ _ (normr (fine (pi / 2)%:E - expR (- x ^+ 2) * J 0))%R).
  rewrite ger0_le_norm ?nnegrE; last 2 first.
  - rewrite -fineB; last 2 first.
    + rewrite J0E.
      rewrite ge0_fin_numE ?ltry// lee_fin.
      by apply: divr_ge0 => //; exact: pi_ge0.
    + rewrite ge0_fin_numE; last first.
        apply: integral_ge0.
        move=> z _.
        rewrite lee_fin.
        by rewrite divr_ge0 ?expR_ge0// ltW.
      apply: (@le_lt_trans _ _ (\int[mu]_(y in `[0%R, +oo[) (dJ 0 y)%:E)).
        apply: ge0_le_integral => //=.
        * move=> ? _.
          rewrite lee_fin.
          by rewrite divr_ge0 ?expR_ge0// ltW.
        * apply/measurable_EFinP.
          apply: measurable_funM.
            apply: measurableT_comp => //.
            apply: measurable_funM => //.
            exact: measurable_funD.
          apply: measurable_funTS.
          exact: continuous_measurable_fun.
        * move=> ? _.
          rewrite lee_fin.
          by rewrite divr_ge0 ?expR_ge0// ltW.
        * apply/measurable_EFinP.
          apply: measurable_funM.
            apply: measurableT_comp => //.
            rewrite expr0n/= oppr0.
            under [X in measurable_fun _ X]eq_fun do rewrite mul0r/=.
            exact: measurable_cst.
          apply: measurable_funTS.
          exact: continuous_measurable_fun.
        move=> z _.
        rewrite lee_fin.
        rewrite ler_pdivlMr// ?divfK; last by rewrite gt_eqF.
        rewrite ler_expR.
        rewrite expr0n/= oppr0 mul0r mulNr oppr_le0.
        by rewrite mulr_ge0 ?sqr_ge0 ?ltW.
      by rewrite J0E ltry.
    rewrite -integralB ?int_J//=.
    apply: fine_ge0.
    apply: integral_ge0 => y _.
    rewrite -EFinD lee_fin.
    rewrite /dJ.
    rewrite -[X in (0 <= _ + X)%R]mulNr.
    rewrite -mulrDl.
    apply: divr_ge0; last by rewrite ltW.
    rewrite expr0n/= oppr0 mul0r subr_ge0 ler_expR.
    rewrite mulNr oppr_le0.
    apply: mulr_ge0; last exact: ltW.
    exact: sqr_ge0.
  - rewrite /J/Rintegral J0E -{1}(mul1r (fine _)) -mulNr -mulrDl.
    apply: mulr_ge0.
      by rewrite subr_ge0 -expR0 ler_expR lerNl oppr0 sqr_ge0.
    by rewrite divr_ge0// pi_ge0.
  rewrite J0E.
  apply: lerB => //.
  rewrite [X in (X * _ <= _)%R](_:_= fine (expR (- x ^+ 2))%:E)//.
  rewrite -fineM; last 2 first.
  - by rewrite ge0_fin_numE ?ltry ?lee_fin ?expR_ge0.
  - rewrite J0E.
    by rewrite ge0_fin_numE ?ltry// lee_fin divr_ge0// pi_ge0.
  apply: fine_le.
  - rewrite J0E -EFinM ge0_fin_numE ?ltry//.
    rewrite lee_fin mulr_ge0 ?expR_ge0//.
    by rewrite divr_ge0// pi_ge0.
  - rewrite -abse_fin_num.
    rewrite ge0_fin_numE; last exact: abse_ge0.
    apply/abse_integralP => //.
      by move/integrableP : (int_J x) => [].
    by move/integrableP : (int_J x) => [].
  rewrite -ge0_integralZl//=; last 3 first.
  - by move/integrableP : (int_J 0%R) => [].
  - move=> y _.
    apply: divr_ge0; last by rewrite ltW.
    by rewrite expr0n/= oppr0 mul0r expR0.
  - by rewrite lee_fin expR_ge0.
  under eq_integral do rewrite -EFinM.
  apply: ge0_le_integral => //=.
  - move=> y _.
    rewrite /dJ expr0n/= oppr0 mul0r expR0 div1r.
    rewrite lee_fin mulr_ge0 ?expR_ge0//.
    by rewrite invr_ge0 ltW.
  - apply/measurable_EFinP.
    apply: measurable_funM => //.
    apply: measurable_funTS.
    under [X in _ _ X]eq_fun.
      move=> y.
      rewrite expr0n/= oppr0 mul0r expR0 div1r.
      over.
    exact: continuous_measurable_fun.
  - move=> y _.
    by rewrite lee_fin divr_ge0// ?expR_ge0 ?ltW.
  - by move/integrableP : (int_J x) => [].
  move=> y _.
  rewrite lee_fin /dJ expr0n oppr0 mul0r expR0 div1r.
  rewrite ler_pM// ?expR_ge0//.
    by rewrite invr_ge0 ltW.
  rewrite expR
rewrite -integralB//=; first last.
- exact: int_J.
- exact: int_J.
have /normr_idP -> : (0 <= (fine
        (\int[lebesgue_measure]_(x0 in `[0, +oo[)
            ((dJ 0 x0)%:E + (- dJ x x0)%:E)%E)))%R.
  apply: fine_ge0.
  apply: integral_ge0 => y _.
  rewrite -EFinD lee_fin subr_ge0.
  rewrite ler_pdivlMr// ?divfK; last by rewrite gt_eqF.
  rewrite ler_expR.
  rewrite expr0n/= oppr0 mul0r mulNr oppr_le0.
  by rewrite mulr_ge0 ?sqr_ge0 ?ltW.
*)


(* ref: https://www.phys.uconn.edu/~rozman/Courses/P2400_17S/downloads/gaussian-integral.pdf *)
Lemma gauss_integration : (\int[mu]_x (gauss x))%R = Num.sqrt pi.
Proof.
have -> : (\int[mu]_x gauss x)%R = (Ig * 2)%R.
  rewrite /Rintegral.
  rewrite ge0_integralT_even//=; last 2 first.
  - rewrite /gauss => x. apply: continuous_comp => /=.
      apply: continuous_comp.
        exact: exprn_continuous.
      exact: continuousN.
    exact: continuous_expR.
  - move=> x.
    by rewrite /gauss fctE sqrrN.
  rewrite [RHS]mulrC. rewrite fineM/=; last 2 first.
      by rewrite ge0_fin_numE//= ltry.
    by rewrite -set_itv_c_infty.
  congr (2%R * _)%R.
  by rewrite -set_itv_c_infty.
rewrite -[RHS](@divfK _ 2)//.
congr (_ * 2)%R.
rewrite -[LHS]ger0_norm; last exact: Rintegral_ge0.
rewrite -[LHS]sqrtr_sqr.
rewrite -(@ger0_norm _ 2)// -(@sqrtr_sqr _ 2)//.
rewrite -sqrtrV//.
rewrite -[RHS]sqrtrM; last exact: pi_ge0.
apply/eqP.
rewrite eqr_sqrt; last 2 first.
    apply: exprn_ge0.
    exact: Rintegral_ge0.
  apply: divr_ge0; first exact: pi_ge0.
  exact: exprn_ge0.
rewrite [X in _ / X]expr2.
rewrite invfM => //.
rewrite mulrA.
apply/eqP.
apply: (@mulIf _ (- 2)%R) => //.
rewrite [RHS]mulrN divfK// mulrC.
apply/esym.
rewrite -[LHS]add0r [LHS]EFinK.
rewrite [RHS]EFinK.
congr (fine _).
rewrite EFinB.
have cdJ x : {for x, continuous (fun x1 : R => (-2 * Ig * gauss x1)%R)}.
  apply: continuousM; first exact: cvg_cst.
  apply: (@continuous_comp _ _ _ (fun x : R => (- (x ^+ 2))%R) expR).
    apply: continuousN.
    exact: exprn_continuous.
  exact: continuous_expR.
rewrite -J0E.
rewrite -[X in 0%:E - X = _]fineK; last by rewrite J0E.
rewrite -(le0_within_pinfty_continuous_FTC2 _ Joo _ _ _ dJE); last 4 first.
- move=> x x0.
  rewrite -mulN1r -!mulrA mulN1r.
  rewrite lerNl oppr0 pmulr_rge0//.
  apply: mulr_ge0 => //.
  exact: Rintegral_ge0.
- apply/continuous_within_itvcyP; split.
    move=> x _; exact: cdJ.
  apply: cvg_at_right_filter; exact: cdJ.
- exact: rcJ0.
- move=> x x0.
  (* lemma *)
  have :  J^`() x = (-2 * Ig * gauss x)%R.
    by apply: dJE; rewrite in_itv/= andbT.
(*
  rewrite /derivable.
  apply/cvg_ex.
  exists (-2 * Ig * gauss x)%R.
  under eq_cvg.
    move=> h/=.
    rewrite /GRing.scale/= mulr1.
    rewrite -RintegralB//.
    over.
  rewrite /=.
  have :  J^`() x = (-2 * Ig * gauss x)%R.
    by apply: dJE; rewrite in_itv/= andbT.
  rewrite derive1E.
  apply/ex_derive1.
  apply: (@ex_derive _ _ _ _ _ _ (-2 * Ig * gauss x)%R).
*)
  admit.
under eq_integral do rewrite !EFinM EFinN !mulNe.
rewrite integral_ge0N; last first.
- move=> x _.
  apply: mulr_ge0 => //; apply: mulr_ge0 => //.
  exact: Rintegral_ge0.
rewrite ge0_integralZl; last 4 first.
- exact: measurable_itv.
- apply: measurable_funTS.
  exact: measurableT_comp.
- by move=> x _; apply: gauss_ge0.
- by apply: mulr_ge0 => //; apply: Rintegral_ge0.
rewrite expr2 mulrA [RHS]EFinM.
rewrite EFinM EFinN !mulNe.
congr (- (_ * _)).
rewrite fineK//.
Admitted.

(*
rewrite itv0ybig.
rewrite -(@le0_nondecreasing_set_cvg_integral _ (fun n => `[0%R, n%:R]%classic)); last 5 first.
- admit.
- admit.
- admit.
- admit.
- admit.

have incr_int_gauss : {homo (fun n =>
          \int[lebesgue_measure]_(x in `[0%R, n%:R]) (gauss x)%:E) : n m /
    (n <= m)%N >-> n <= m}.
  apply/nondecreasing_seqP => n.
  apply: ge0_subset_integral => //=; last 2 first.
      move=> ? _; exact: gauss_ge0.
    by apply: set_interval.subset_itvl; rewrite bnd_simp ler_nat.
  apply: measurableT_comp => //.
  apply: measurableT_comp => //.
  exact: measurableT_comp.
have decr_int :
  {homo (fun n =>
          \int[lebesgue_measure]_(x in `[0%R, n%:R]) (-2 * Ig * gauss x)%:E) : n m /
   (n <= m)%N >-> m <= n}.
  move=> n m nm.
  under eq_integral do rewrite EFinM.
  under [leRHS]eq_integral do rewrite EFinM.
  have intIg k : lebesgue_measure.-integrable `[0%R, k%:R]%classic (cst Ig%:E).
    apply/integrableP; split; first exact: measurable_cst.
    have [_ _] := locally_integrable_cst Ig.
    move/(_ `[0%R, k%:R]%classic).
    have sub0kT : `[0%R, k%:R] `<=` [set: R] by []; move/(_ sub0kT) => {sub0kT}.
    move/(_ (@segment_compact _ _ _)).
    by under eq_integral do rewrite -normr_EFin; move=> /=.
  rewrite !integralZl//=.
  rewrite !mulNr EFinN !mulNe.
  rewrite leeN2.
  rewrite lee_pmul//.
      by rewrite lee_fin mulr_ge0// Rintegral_ge0.
    by rewrite integral_ge0// => ? _; rewrite lee_fin.
  exact: incr_int_gauss.
have /cvg_lim <- // := ereal_nonincreasing_cvgn decr_int.
apply/cvg_lim => //.
rewrite expr2 mulrA EFinM.
under eq_cvg.
  move=> n.
  under eq_integral do rewrite EFinM.
  rewrite integralZl//=.
  over.
apply: (@cvgeMl _ _ _ _ Ig%:E (-2 * Ig)%:E) => //.
have := (@ereal_nondecreasing_cvgn _ (fun n => \int[lebesgue_measure]_(x in `[0%R, n%:R]) (gauss x)%:E)).
move/(_ incr_int_gauss).
rewrite ge0_nondecreasing_set_cvg_integral; last 5 first.
- apply/nondecreasing_seqP => n.
  rewrite subsetEset.
  by apply: set_interval.subset_itvl; rewrite bnd_simp ler_nat.
- move=> n; exact: measurable_itv.
- apply: bigcup_measurable.
  move=> n _; exact: measurable_itv.
- apply: measurable_funTS => /=.
  apply: measurableT_comp => //.
  apply: measurableT_comp => //.
  exact: measurableT_comp.
- move=> x _; exact: gauss_ge0.
rewrite /Ig itv0ybig.
rewrite fineK//.
rewrite ge0_fin_numE; last by apply: integral_ge0 => n _; apply: gauss_ge0.
pose seq_geo := series (geometric (expR 1%R) (@expR R (- 1)%R)).
apply: (@le_lt_trans _ _ (limn (EFin \o seq_geo))); last first.
  admit.
rewrite -eq_bigcup_seqD.
rewrite ge0_integral_bigcup; last 4 first.
- case =>  /=[|n].
    by rewrite set_interval.set_itv1.
  exact: measurableD.
- apply: measurableT_comp => //.
  apply: measurableT_comp => //.
  by apply: measurableT_comp.
- move=> n _; exact: gauss_ge0.
- apply: trivIset_seqD.
  apply/nondecreasing_seqP => n.
  rewrite subsetEset.
  by apply: set_interval.subset_itvl; rewrite bnd_simp ler_nat.
rewrite /seq_geo.
rewrite /series.
rewrite /geometric/=.
rewrite fctE.
rewrite (_: limn (fun x => (\sum_(0 <= k < x) expR 1%R * expR (- 1) ^+ k)%:E)
  =  limn (fun x => (\sum_(0 <= k < x) (expR 1%R * expR (- k%:R))%:E))); last first.
  congr (limn _).
  apply/funext => n.
  rewrite sumEFin.
  congr (EFin _).
  apply: eq_bigr => k _.
  by rewrite -expRM_natr mulr_natr mulNrn.
apply: lee_nneseries.
  move=> n _.
  apply: integral_ge0 => x _; exact: gauss_ge0.
rewrite /seqD.
case =>[_|n _].
  rewrite set_interval.set_itv1 integral_set1 oppr0 expR0 mulr1.
  exact: expR_ge0.
rewrite -[leRHS]mule1.
rewrite (_:1%E = mu `]n%:R, n.+1%:R]); last first.
  rewrite /mu lebesgue_measure_itv/= lte_fin ltr_nat ltnS leqnn.
  by rewrite -EFinD -natrB// subSnn.
rewrite -[leRHS]integral_cst/=; last exact: measurable_itv.
rewrite [X in \int[_]_(_ in X) _ <= _](_:_= `]n%:R, n.+1%:R]%classic); last first.
  rewrite eqEsubset; split => x/=.
    move=> []; rewrite !in_itv/=.
    move=> /andP[x0 xSn].
    move=> /negP/nandP.
    rewrite x0/= => -[]//.
    by rewrite -ltNge => ->.
  rewrite !in_itv/= => /andP[nx xSn]; split.
    rewrite xSn andbT ltW//.
    apply: le_lt_trans nx.
    by rewrite {1}(_:1%R = 1%N%:R)// ltr_nat.
  by apply/negP/nandP; right; rewrite -ltNge.
apply: le_integral => //=.
    apply: (@integrableS _ _ _ lebesgue_measure `[0%R, n.+1%:R]) => //.
    by apply: set_interval.subset_itvr; rewrite bnd_simp.
  apply/integrableP; split => //.
  apply/abse_integralP => //.
  rewrite -fin_num_abs ge0_fin_numE/=; last first.
    apply: integral_ge0 => ? _.
    by rewrite lee_fin -expRD expR_ge0.
  rewrite integral_cst//=.
  rewrite lebesgue_measure_itv/= lte_fin ltr_nat leqnn.
  rewrite -EFinB -EFinM ltey//.
move=> x; rewrite inE/= in_itv/= => /andP[nx xSn].
rewrite -expRD.
rewrite lee_fin.
rewrite ler_expR.
rewrite mulrS opprD addrA subrr sub0r.
rewrite lerN2.
rewrite ltW//.
case: n nx xSn => [x0 _|n Snx _].
  by rewrite exprn_gt0.
apply: (lt_trans Snx).
rewrite lter_eXnr//.
apply: le_lt_trans Snx.
by rewrite {1}(_:1%R = 1%:R)// ler_nat.
Admitted.
*)

End Gauss_integration.
