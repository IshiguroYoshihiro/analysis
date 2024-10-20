Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum exp.
Require Import measure lebesgue_measure numfun lebesgue_integral itv.
Require Import realfun derive.
Require Import trigo.
Require Import ftc.

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
Admitted.

End continuous_change_of_variables.

(*============================================================================*)
(* from lang_syntax.v in branch prob_lang_axiom by IshiguroYoshihiro *)
(* https://github.com/IshiguroYoshihiro/analysis/tree/prob_lang_axiom *)
Section left_continuousW.

Notation left_continuous f :=
  (forall x, f%function @ at_left x --> f%function x).

Lemma left_continuousW (R : numFieldType) (f : R -> R) :
  continuous f -> left_continuous f.
Proof. Admitted.

End left_continuousW.

Lemma exprn_derivable {R : realType} (n : nat) (x : R):
  derivable ((@GRing.exp R) ^~ n) x 1.
Proof.
Admitted.

(*============================================================================*)
(* my works begin here *)

(* TODO: PR *)
Lemma lt_atan {R : realType} : {homo (@atan R) : x y / (x < y)%R}.
Proof.
move=> x y xy; rewrite -subr_gt0.
have datan z : z \in `]x, y[ -> is_derive z 1%R atan (1 + z ^+ 2)^-1.
  by move=> _; exact: is_derive1_atan.
have catan : {within `[x, y], continuous atan}.
  by apply: derivable_within_continuous => z _; exact: ex_derive.
have [c] := MVT xy datan catan.
have [-> _ ->|c0 _ ->] := eqVneq c 0%R.
  by rewrite expr0n/= addr0 invr1 mul1r subr_gt0.
by rewrite mulr_gt0 ?subr_gt0// invr_gt0 addr_gt0// exprn_even_gt0.
Qed.

Lemma nondecreasing_atan {R : realType} : {homo @atan R : x y / (x <= y)%R}.
Proof.
by move=> x y; rewrite le_eqVlt => /predU1P[-> //|xy]; exact/ltW/lt_atan.
Qed.

(* TODO: PR *)
Lemma atan_pinfty_pi2 {R : realType} : (@atan R) x @[x --> +oo%R] --> pi / 2.
Proof.
rewrite (_: pi / 2 = sup (range atan)).
  apply: (nondecreasing_cvgr nondecreasing_atan); exists (pi / 2)%R.
  by move=> _ /= [x _ <-]; exact/ltW/atan_ltpi2.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: sup_le_ub.
    by exists 0%R, 0%R => //; exact: atan0.
  by move=> _ /= [x _ <-]; exact/ltW/atan_ltpi2.
have -> : pi / 2 = sup `[0%R, pi / 2[%classic :> R.
  by rewrite real_interval.sup_itv// bnd_simp divr_gt0// pi_gt0.
apply: le_sup; last 2 first.
- by exists 0%R; rewrite /= in_itv/= lexx/= divr_gt0// pi_gt0.
- split; first by exists 0%R, 0%R => //; rewrite atan0.
  by exists (pi / 2)%R => _ [x _ <-]; exact/ltW/atan_ltpi2.
move=> x/= /[!in_itv]/= /andP[x0 xpi2].
apply/downP; exists (atan (tan x)) => /=; first by exists (tan x).
rewrite tanK// in_itv/= xpi2 andbT (lt_le_trans _ x0)//.
by rewrite ltrNl oppr0 divr_gt0// pi_gt0.
Qed.

Lemma cvgr_expR {R : realType} : @expR R (- x) @[x --> +oo%R] --> 0%R.
Proof.
apply/cvgrPdist_le => e e0; near=> x.
rewrite sub0r normrN ger0_norm; last exact: expR_ge0.
rewrite expRN -[leRHS]invrK lef_pV2 ?posrE ?expR_gt0 ?invr_gt0//.
rewrite (le_trans _ (expR_ge1Dx _))// -lerBlDl.
by near: x; apply: nbhs_pinfty_ge; exact: num_real.
Unshelve. end_near. Qed.

Lemma cvgn_expR {R : realType} : @expR R (1%R *- n) @[n --> \oo] --> 0%R.
Proof.
under eq_cvg do rewrite -mulNrn -mulr_natr expRM_natr.
apply: cvg_expr.
by rewrite expRN ger0_norm ?invr_ge0 ?expR_ge0// invf_lt1 ?expR_gt1 ?expR_gt0.
Qed.

Section within_continuous_FTC2_pinfty.
Notation mu := lebesgue_measure.

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
apply: ge0_nondecreasing_set_cvg_integral => //.
  exact: measurableT_comp.
move=> x Sx.
rewrite leeNr oppe0.
exact: f0.
Abort.

Lemma ge0_Rceil_nat {R : realType} (x : R) : (0 <= x)%R ->
  exists n, n%:R = Rceil x.
Proof.
move=> x0.
have := isint_Rceil x.
  move/RintP => [z cxz].
have : Rceil x \is a int_num.
  rewrite archimedean.Num.Theory.intrEceil.
  by rewrite archimedean.Num.Theory.intrKceil.
rewrite archimedean.Num.Theory.intrEge0; last exact: Rceil_ge0.
move/archimedean.Num.Theory.natrP => {z cxz}[n cxn].
by exists n.
Qed.

(* same as real_interval.itv_bnd_inftyEbigcup *)
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
  have incr_sumf: {homo (fun i : nat => (\sum_(n <= k < i) ((f k.+1)%:E - (f k)%:E)%E)%R) : n0 m / 
   (n0 <= m)%N >-> n0 <= m}.
    apply/nondecreasing_seqP => m.
rewrite -subre_ge0; last first.
  apply/sum_fin_numP => /= ?  _.
  by rewrite -EFinD.
have [nm|mn]:= ltnP m n; last 2 first.
    rewrite !big_nat !big_pred0//.
      move=> k.
      apply/negP => /andP[] /leq_ltn_trans => H /H{H}.
      apply/negP.
      by rewrite ltn_geF// ltnW.
    move=> k.
    apply/negP => /andP[] /leq_ltn_trans => H /H{H}.
    apply/negP.
    by rewrite ltn_geF// ltnW.
rewrite !telescope_sume//; last exact: leqW.
by rewrite oppeB// addeCA subeK// addeC sube_ge0// lee_fin nondecf.
have -> : limn (EFin \o f) - (f n)%:E =
    ereal_sup (range (fun n0 => \sum_(n <= k < n0) ((f k.+1)%:E - (f k)%:E)%E)).
  transitivity (limn (((EFin \o f) \- (cst (f n)%:E)))).
    apply/esym.
    apply/cvg_lim => //.
    apply: cvgeB.
        exact: fin_num_adde_defl.
      apply: ereal_nondecreasing_is_cvgn.
      by move=> x y xy; rewrite lee_fin; apply: nondecf.
    apply: cvg_EFin.
      by apply: nearW => x.
    exact: cvg_cst.
  have := (@ereal_nondecreasing_cvgn _ (fun i =>  (\sum_(n <= k < i) ((f k.+1)%:E - (f k)%:E)%E)%R)).
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
exact: ereal_nondecreasing_cvgn.
Qed.

Lemma ge0_within_pinfty_continuous_FTC2 {R : realType} (f F : R -> R) a (l : R) :
  (forall x, (a <= x)%R -> 0 <= f x)%R ->
  F x @[x --> +oo%R] --> l ->
  (* {within `[a, +oo[, continuous f} *)
  f x @[x --> a^'+] --> f a ->
  (forall x, (a < x)%R -> {for x, continuous f}) ->
  (* derivable_oo_continuous_bnd F a +oo *)
  (forall x, (a < x)%R -> derivable F x 1) ->
  F x @[x --> a^'+] --> F a ->
  {in `]a, +oo[, F^`() =1 f} ->
  (\int[lebesgue_measure ]_(x in `[a, +oo[) (f x)%:E = l%:E - (F a)%:E)%E.
Proof.
have zeroR : (@GRing.zero R = 0%:R) by [].
move=> f_ge0 Fxl fa cf dF Fa dFE.
rewrite -integral_itv_obnd_cbnd; last first.
  apply: open_continuous_measurable_fun.
    exact: interval_open.
  move=> x; rewrite inE/= in_itv/= => /andP[ax _].
  exact: cf.
rewrite itv_bnd_infty_bigcup.
rewrite seqDU_bigcup_eq.
have seqDUE (k : nat) : seqDU (fun k0 => `]a, (a + k0%:R)%R]%classic) k = `](a + k.-1%:R), (a + k%:R)%R]%classic.
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
        by rewrite lerDl zeroR// ler_nat.
      + apply/negP; rewrite negb_and; apply/orP; right.
        by rewrite -real_ltNge//=.
  apply/nondecreasing_seqP => n.
  rewrite subsetEset => x/=; rewrite !in_itv/=.
  move/andP => [-> xan]/=.
  apply: (le_trans xan).
  by rewrite lerD// ler_nat.
rewrite ge0_integral_bigcup//=; last 3 first.
- move=> k.
  apply: measurableD => //.
  exact: bigsetU_measurable.
- rewrite -seqDU_bigcup_eq.
  rewrite -itv_bnd_infty_bigcup.
  apply: measurableT_comp => //.
  apply: open_continuous_measurable_fun => //.
    exact: interval_open.
  move=> x; rewrite inE/= in_itv/= => /andP[ax _].
  exact: cf.
- move=> x.
  rewrite -seqDU_bigcup_eq.
  rewrite -itv_bnd_infty_bigcup.
  rewrite /= in_itv/= => /andP[/ltW ax _].
  rewrite lee_fin.
  exact: f_ge0.
have dFEn n : {in `]a + n%:R, a + n.+1%:R[, F^`() =1 f}.
  apply: in1_subset_itv dFE.
  move=> x/=; rewrite !in_itv/= andbT=> /andP[+ _].
  apply: le_lt_trans.
  by rewrite lerDl zeroR ler_nat.
have Fshiftn_liml : limn (EFin \o (fun k : nat => F (a + k%:R))) = l%:E.
  apply/cvg_lim => //.
  apply: cvg_EFin; first by apply: nearW => ?.
  apply: ((cvg_pinftyP F l).1 Fxl).
  apply/cvgryPge.
  move=> r.
  near=> n.
  rewrite -lerBlDl.
  near: n.
  exact: nbhs_infty_ger.
transitivity (\big[+%R/0%R]_(0 <= i <oo)
  ((F (a + i.+1%:R))%:E - (F (a + i%:R))%:E)).
  transitivity (\big[+%R/0%R]_(0 <= i <oo) \int[lebesgue_measure]_(x in
         seqDU (fun k : nat => `]a, (a + k%:R)]%classic) i.+1) (f x)%:E).
    apply/cvg_lim => //.
      rewrite -cvg_shiftS.
      under eq_cvg.
      move=> k /=.
      rewrite (big_cat_nat _ _ _ (leqnSn 0%N))//=.
      rewrite big_nat1/= /seqDU addr0 set_itvoc0 set0D integral_set0 add0r.
      rewrite big_add1 succnK.
      over.
    apply: cvg_toP => //.
    apply: is_cvg_nneseries => n _.
    rewrite integral_ge0//.
    move=> /= x[]; rewrite in_itv/= => /andP[ax _] _.
    rewrite lee_fin.
    by apply: f_ge0; rewrite ltW.
  apply: eq_eseriesr => n _.
  rewrite seqDUE/=.
  rewrite integral_itv_obnd_cbnd; last first.
    rewrite -setUitv1; last first.
      rewrite bnd_simp.
      by apply: ler_ltD => //; rewrite ltr_nat.
    rewrite measurable_funU//; split; last exact: measurable_fun_set1.
    apply: open_continuous_measurable_fun => //; first exact: interval_open.
    move=> x; rewrite inE/= in_itv/= => /andP[anx _].
    apply: cf.
    apply: le_lt_trans anx.
    by rewrite lerDl zeroR// ler_nat.
  apply: continuous_FTC2 (dFEn n).
  - by apply: ler_ltD => //; rewrite ltr_nat.
  - apply/continuous_within_itvP; first by apply: ler_ltD => //; rewrite ltr_nat.
    split.
    + move=> x.
      rewrite in_itv/= => /andP[xan _].
      apply: cf.
      apply: le_lt_trans xan.
      by rewrite lerDl zeroR// ler_nat.
    + case : n; first by rewrite addr0.
      move=> n.
      apply: cvg_at_right_filter.
      apply: cf.
      by rewrite ltrDl zeroR ltr_nat.
    + apply: cvg_at_left_filter.
      apply: cf.
      by rewrite ltrDl zeroR ltr_nat.
  - split.
    + move=> x; rewrite in_itv/= => /andP[anx _].
      apply: dF.
      apply: le_lt_trans anx.
      by rewrite lerDl zeroR ler_nat.
    + case : n; first by rewrite addr0.
      move=> n.
      have : {within `[(a + n.+1%:R)%R, (a + n.+2%:R)%R], continuous F}.
        apply: derivable_within_continuous.
        move=> x; rewrite in_itv/= => /andP[aSn _].
        apply: dF.
        apply: lt_le_trans aSn.
        by rewrite ltrDl zeroR ltr_nat.
      move/continuous_within_itvP.
      have aSnaSSn: (a + n.+1%:R < a + n.+2%:R)%R.
        apply: ler_ltD => //.
        by rewrite ltr_nat.
      by move/(_ aSnaSSn) => [].
  - have : {within `[(a + n%:R + 2^-1)%R, (a + n.+1%:R)%R], continuous F}.
      apply: derivable_within_continuous.
      move=> x; rewrite in_itv/= => /andP[aSn _].
      apply: dF.
      apply: lt_le_trans aSn.
      rewrite -addrA ltrDl.
      by rewrite -[ltLHS]addr0 ler_ltD.
    move/continuous_within_itvP.
    have an2vaSn : (a + n%:R + 2^-1 < a + n.+1%:R)%R.
      rewrite -addrA ler_ltD//.
      rewrite -[ltRHS]natr1 ler_ltD//.
      rewrite invf_lt1//.
      by rewrite (_:1%R = 1%:R)// ltr_nat.
    by move/(_ an2vaSn) => [].
rewrite increasing_telescope_sume_infty_fin_num; last 2 first.
  rewrite Fshiftn_liml//.
  apply/nondecreasing_seqP => n.
  rewrite -subr_ge0.
  have isdF x : x \in `](a + n%:R)%R, (a + n.+1%:R)%R[ -> is_derive x 1%R F (f x).
    rewrite in_itv/= => /andP[anx _].
    rewrite -dFE; last first. 
    rewrite in_itv/= andbT.
    apply: le_lt_trans anx.
    by rewrite lerDl zeroR.
    rewrite derive1E.
    apply: derivableP.
    apply: dF.
    apply: le_lt_trans anx.
    by rewrite lerDl zeroR.
  have [| |r ranaSn ->] := (MVT _ isdF).
  - by apply: ler_ltD => //; rewrite ltr_nat.
  - case : n isdF => [_ |n _].
      apply/continuous_within_itvP; first by rewrite ler_ltD// ltr_nat.
      rewrite addr0.
      split => //.
        move=> x; rewrite in_itv/= => /andP[ax _].
        apply: differentiable_continuous.
        apply/derivable1_diffP.
        exact: dF.
      apply: cvg_at_left_filter.
      apply: differentiable_continuous.
      apply/derivable1_diffP.
      apply: dF.
      by rewrite ltr_pwDr.
    apply: derivable_within_continuous => x; rewrite in_itv/= => /andP[aSnx _].
    apply: dF.
    apply: lt_le_trans aSnx.
    by rewrite ltrDl.
  move: ranaSn; rewrite in_itv/= => /andP[/ltW anr _].
  apply: mulr_ge0.
    apply: f_ge0.
    apply: le_trans anr.
    by rewrite lerDl.
  by rewrite [X in (0 <= X - _)%R]addrC addrKA subr_ge0 ler_nat.
by rewrite addr0 EFinN; congr (_ - _).
Unshelve. end_near. Qed.

Lemma le0_within_pinfty_continuous_FTC2 {R : realType} (f F : R -> R) a (l : \bar R) :
  (forall x, (a <= x)%R -> f x <= 0)%R ->
  (F x)%:E @[x --> +oo%R] --> l ->
  (* {within `[a, +oo[, continuous f} *)
  f x @[x --> a^'+] --> f a ->
  (forall x, (a < x)%R -> {for x, continuous f}) ->
  (* derivable_oo_continuous_bnd F a +oo *)
  (forall x, (a < x)%R -> derivable f x 1) ->
  {in `]a, +oo[, F^`() =1 f} ->
  (\int[lebesgue_measure ]_(x in `[a, +oo[) (f x)%:E = l - (F a)%:E)%E.
Proof.
move=> f_ge0 + fa cf df dFE.
case: l; last 2 first.
Admitted.

End within_continuous_FTC2_pinfty.


Section Gamma.

Context {R : realType}.

Let mu := @lebesgue_measure R.

(* NB: also defined in prob_lang_wip*)
Definition Gamma (a : R) : \bar R :=
  (\int[mu]_(x in `[0%R, +oo[) (powR x (a - 1) * expR (- x))%:E)%E.

Let I n := \int[mu]_(x in `[0%R, +oo[) (x ^+ n * expR (- x))%:E.

Let I0 : I O = 1.
rewrite /I.
(under eq_integral do rewrite expr0 mul1r) => /=.
have expRN1 : (fun x => @expR R (- x)) = fun x => (expR x)^-1.
  apply/funext => z.
  by rewrite expRN.
(* improper intergral *)
have <- : lim ((\int[mu]_(x in `[0%R, n.+1%:R]) (expR (- x))%:E) @[n --> \oo]) = \int[mu]_(x in `[0%R, +oo[) (expR (- x))%:E.
  apply/cvg_lim => //.
  rewrite (_: \int[mu]_(x in `[0%R, +oo[) (expR (- x))%:E = ereal_sup (range (fun n => \int[mu]_(x in `[0%R, n.+1%:R]) (expR (- x))%:E))); last first.
    apply/eqP; rewrite eq_le; apply/andP; split.
      rewrite (_:`[0%R, +oo[%classic = \bigcup_i `[0%R, i.+1%:R]%classic); last first.
        rewrite eqEsubset; split.
          move=> /= x/=; rewrite in_itv/= => /andP[x0 _].
          have := Rceil_ge0 x0.
          have := isint_Rceil x.
          move/RintP => [z cxz].
          rewrite ler0z.
          rewrite -ssrint.mc_2_0.Znat_def.
          move/mc_2_0.natrP => [n zn].
          exists n => //=.
          rewrite /= in_itv/= x0/=.
          apply: (le_trans (Rceil_ge _)).
          rewrite RceilE zn ltW// -natr1.
          apply: ltr_pwDr => //.
          by rewrite natz.
        by move=> /= x [n _]/=; rewrite !in_itv/= => /andP[->].
      (* applying improper integral *)
      rewrite -ge0_nondecreasing_set_cvg_integral//; last 2 first.
          apply: measurable_funTS.
          apply: (measurable_comp measurableT) => //.
          exact: (measurable_comp measurableT).
        by move=> ? _; apply: expR_ge0.
      apply/nondecreasing_seqP => n.
      rewrite subsetEset => x/=.
      rewrite !in_itv/= => /andP[-> xnS]/=.
      apply: (le_trans xnS).
      by rewrite ler_nat.
    apply: ub_ereal_sup.
    move=> _/= [n _ <-].
    apply: ge0_subset_integral => //; last 2 first.
        by move=> ? _; apply: expR_ge0.
      by move=> x/=; rewrite !in_itv/=; move/andP => [->].
    apply: measurable_funTS => /=.
    apply: (measurable_comp measurableT) => //.
    exact: (measurable_comp measurableT).
  apply: ereal_nondecreasing_cvgn.
  apply/nondecreasing_seqP => n.
  apply: (@ge0_subset_integral _ _ _ mu) => //.
      apply: measurable_funTS.
      apply: (measurable_comp measurableT) => //.
      exact: (measurable_comp measurableT).
    by move => ? _; apply: expR_ge0.
  move=> x /=.
  rewrite !in_itv/= => /andP[-> xnS]/=.
  apply: (le_trans xnS).
  by rewrite ler_nat.
rewrite -{1}(@add0e _ 1).
apply/cvg_lim => //.
under eq_cvg => n.
  rewrite (@continuous_FTC2 _ (fun x => expR (- x)) (fun x => - expR (- x))%R 0%R n.+1%:R)//; last 3 first.
  - rewrite expRN1.
    apply: continuous_subspaceT.
    move=> x.
    apply: continuousV.
      apply: lt0r_neq0.
      exact: expR_gt0.
    exact: continuous_expR.
  - have cX : continuous (fun x : R => (- expR (- x))%R).
      move=> /= x; rewrite /continuous_at.
      apply: cvgN.
      rewrite expRN1.
      rewrite [X in _ --> X](_:_= (expR x)^-1)%R; last first.
        suff : (fun x => @expR R (- x)) =1 (fun x => (expR x)^-1) by [].
        by rewrite -funeqE.
      apply: cvgV.
        apply: lt0r_neq0.
        exact: expR_gt0.
      exact: continuous_expR.
    split.
    + by [].
    + exact: right_continuousW.
    + exact: left_continuousW.
  - move=> x _.
    rewrite derive1E.
    rewrite deriveN//=.
    rewrite -derive1E.
    rewrite derive1_comp//.
    rewrite !derive1E.
    rewrite deriveN//.
    rewrite mulrN opprK.
    rewrite (_:'D_1 expR (- x) = expR (- x))//; last exact: derive_val.
    rewrite -[RHS]mulr1.
    apply: f_equal.
    exact: derive_val.
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
apply: cvg_EFin; first by apply/nearW.
exact: cvgn_expR.
Qed.

Let I_rec n : I n.+1 = n.+1%:R%:E * I n.
(* using integration by parts *)
Proof.
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
Admitted.

End Rceil_lemma.

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
- by move/EFin_measurable_fun : mf; rewrite /D big_cons.
- apply/eqP; rewrite big_distrr/= big_seq big1// => i it.
  move/trivIsetP : tF; apply => //=; rewrite ?mem_head//.
  + by rewrite inE it orbT.
  + by apply/eqP => hi; move: us => /=; rewrite hi it.
Qed.

End integral_bigsetU.

From mathcomp Require Import archimedean.

Section itv_bnd_infty_bigcup_shiftn.

Lemma itv_bnd_infty_bigcup_shiftn (R : realType) b (x : R) (n : nat):
  [set` Interval (BSide b x) +oo%O] =
  \bigcup_i [set` Interval (BSide b x) (BLeft (x + (i + n)%:R))].
Proof.
apply/seteqP; split=> y; rewrite /= !in_itv/= andbT; last first.
  by move=> [k _ /=]; move: b => [|] /=; rewrite in_itv/= => /andP[//] /ltW.
move=> xy; exists (`|Num.ceil (y - x)|)%N => //=. Admitted.
(* rewrite in_itv/= xy/= -lerBlDl.
apply: (@le_trans _ _ (`|Num.ceil (y - x)|)%N%:R); last by rewrite natrD lerDl.
rewrite !natr_absz/= ger0_norm -?ceil_ge0 ?ceil_ge//; last first.
rewrite (lt_le_trans (ltrN10 R))// subr_ge0.
by case: b xy => //= /ltW.
Qed.
*)

Lemma itv_bnd_infty_bigcup_shiftS (R : realType) b (x : R):
  [set` Interval (BSide b x) +oo%O] =
  \bigcup_i [set` Interval (BSide b x) (BLeft (x + i.+1%:R))].
Proof.
under eq_bigcupr do rewrite -addn1.
exact: itv_bnd_infty_bigcup_shiftn.
Qed.

(* *)
Section near_in_itv_yy.

Local Import real_interval.

Lemma near_in_itv_oy {R : realFieldType} (a : R) :
  {in `]a, +oo[, forall y, \forall z \near y, z \in `]a, +oo[}.
Proof.
move=> x ax.
near=> z.
suff : z \in `]a, +oo[%classic by rewrite inE.
near: z.
rewrite near_nbhs.
apply: (@open_in_nearW _ _ `]a, +oo[%classic) => //.
by rewrite inE/=.
Unshelve. end_near. Qed.

Lemma near_in_itv_yo {R : realFieldType} (b : R) :
  {in `]-oo, b[, forall y, \forall z \near y, z \in `]-oo, b[}.
Proof.
move=> x xb.
near=> z.
suff : z \in `]-oo, b[%classic by rewrite inE.
near: z.
rewrite near_nbhs.
apply: (@open_in_nearW _ _ `]-oo, b[%classic) => //.
by rewrite inE/=.
Unshelve. end_near. Qed.

Lemma near_in_itv_yy {R : realFieldType} :
  {in `]-oo, +oo[, forall y : R, \forall z \near y, z \in `]-oo, +oo[}.
Proof.
move=> x _.
rewrite -near_nbhs.
exact: nearW => //.
Qed.

End near_in_itv_yy.


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
  (* {within `]-oo, F a[, continuous G *)
  {in `]-oo, F a[, continuous G} ->
  (G x @[x --> (F a)^'-] --> G (F a)) ->
  F x @[x --> +oo%R] --> -oo%R ->
  {in `]-oo, F a], forall x, (0 <= G x)%R} ->
  \int[mu]_(x in `]-oo, F a]) (G x)%:E =
  \int[mu]_(x in `[a, +oo[) (((G \o F) * - F^`()) x)%:E.
Proof.
move=> decrF cdF /cvg_ex[/= dFa cdFa] /cvg_ex[/= dFoo cdFoo].
move=> cFa dF cG cGFa Fny G0.
have mG n : measurable_fun `](F (a + n.+1%:R)), (F a)] G.
  rewrite -setUitv1; last first.
    rewrite bnd_simp.
    by apply: decrF; rewrite ?in_itv/= ?andbT// ?ltW// ltrDl.
  apply/measurable_funU => //; split; last exact: measurable_fun_set1.
  apply: open_continuous_measurable_fun; first exact: interval_open.
  move=> x; rewrite inE/= in_itv/= => /andP[_ xFa].
  by apply: cG; rewrite in_itv/=.
have mGFNF' i : measurable_fun `[a, (a + i.+1%:R)[ ((G \o F) * - F^`())%R.
  rewrite -setU1itv; last first.
    rewrite bnd_simp.
    by rewrite ?in_itv/= ?andbT// ?ltW// ltrDl.
  rewrite measurable_funU//; split; first exact: measurable_fun_set1.
  apply: measurable_funM.
    apply: (measurable_comp (measurable_itv `]F (a + i.+1%:R), F a[)).
        move=> _/= [x + <-].
        rewrite !in_itv/= => /andP[ax aSi]; apply/andP.
        by split; apply: decrF; rewrite ?in_itv//= ?lexx ?ltW ?ltrDl.
      apply: open_continuous_measurable_fun; first exact: interval_open.
      move=> y; rewrite inE/= in_itv/= => /andP[_ xFa].
      by apply: cG; rewrite in_itv/=.
    apply: open_continuous_measurable_fun.
    exact: interval_open.
    move=> x; rewrite inE/= in_itv/= => /andP[ax _].
    apply: differentiable_continuous.
    apply/derivable1_diffP.
    by apply: dF; rewrite in_itv/= ax.
  apply: open_continuous_measurable_fun.
    exact: interval_open.
  move=> x; rewrite inE/= in_itv/= => /andP[ax _].
  apply: continuousN.
  apply: cdF.
  by rewrite in_itv/= ax.
transitivity (limn (fun n => \int[mu]_(x in `[F (a + n%:R)%R, F a]) (G x)%:E)).
  rewrite (decreasing_fun_itv_infty_bnd_bigcup decrF Fny).
  rewrite seqDU_bigcup_eq.
  rewrite ge0_integral_bigcup/=; first last.
  - exact: trivIset_seqDU.
  - rewrite -seqDU_bigcup_eq.
    move=> x [n _ /=]; rewrite in_itv/= => /andP[_ xFa].
    exact: G0.
  - rewrite -seqDU_bigcup_eq.
    apply/EFin_measurable_fun.
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
  - apply/EFin_measurable_fun.
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
    apply/EFin_measurable_fun.
    apply: measurable_funS (mGFNF' n) => //.
    exact: subset_itv_oo_co.
  - move=> x ax.
    have {ax}ax : (a < x)%R.
      move: ax.
      rewrite -seqDU_bigcup_eq => -[? _]/=.
      by rewrite in_itv/= => /andP[].
    rewrite fctE.
    apply: mulr_ge0.
    + apply: G0.
      rewrite in_itv/= ltW//.
      by apply: decrF; rewrite ?in_itv/= ?lexx// ltW.
    + rewrite oppr_ge0.
 (* TODO: lemma : nonincreasing -> derive <= 0%R *)
      apply: limr_le.
        (* TODO: lemma, derivable F x 1 := cvg ... (h%:A + x) ...
           so we cannot apply dF directly *)
        move: (dF x); rewrite in_itv/= ax/=.
        rewrite /derivable/=.
        have scaleR1 h : GRing.scale h (GRing.one R) = h by rewrite /GRing.scale/= mulr1.
        under eq_fun do rewrite scaleR1.
        exact.
      near=> h.
  (* lemma? *)
      have : h != 0%R by near: h; exact: nbhs_dnbhs_neq.
      rewrite neq_lt => /orP[h0|h0].
      + rewrite nmulr_rle0 ?invr_lt0// subr_ge0.
        rewrite ltW//.
        apply: decrF; rewrite ?in_itv/= ?andbT ?ltW ?gtrDr//.
        rewrite -ltrBlDr.
        rewrite -ltrN2.
        apply: ltr_normlW; rewrite normrN.
        near: h.
        apply: dnbhs0_lt.
        by rewrite opprB subr_gt0.
      + rewrite pmulr_rle0 ?invr_gt0// subr_le0 ltW//.
        apply: decrF; rewrite ?in_itv/= ?andbT ?ltrDr// ltW//.
        rewrite -ltrBlDr -ltrN2.
        apply: ltr_normlW; rewrite normrN.
        near: h.
        apply: dnbhs0_lt.
        by rewrite opprB subr_gt0.
  - exact: trivIset_seqDU.
  apply: congr_lim.
  apply/funext => n.
  rewrite -integral_bigsetU_EFin/=; last 4 first.
  - move=> k.
    apply: measurableD => //.
    exact: bigsetU_measurable.
  - exact: iota_uniq.
  - exact: (@sub_trivIset _ _ _ [set: nat]).
  - apply/EFin_measurable_fun.
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
    apply: cG.
    rewrite in_itv/=.
    apply: decrF.
    * by rewrite in_itv/= andbT lerDl.
    * by rewrite in_itv/= lexx.
    * by rewrite ltr_pwDr.
  + exact: cGFa.
Unshelve. end_near. Qed.

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
  {in `]-oo, (- a)%R[, continuous G} ->
  (G x @[x --> (- a)%R^'-] --> G (- a)%R) ->
  {in `]-oo, (- a)%R], forall x, (0 <= G x)%R} ->
  \int[mu]_(x in `]-oo, (- a)%R]) (G x)%:E =
  \int[mu]_(x in `[a, +oo[) ((G \o -%R) x)%:E.
Proof.
move=> cG GNa G0.
have Dopp : (@GRing.opp R)^`() = cst (-1).
  by apply/funext => z; rewrite derive1E derive_val.
rewrite ge0_integration_by_substitution_decreasing_opinfty//; last 6 first.
- by move=> x y _ _; rewrite ltrN2.
- rewrite Dopp => ? _.
  exact: cst_continuous.
- rewrite Dopp; apply: is_cvgN; exact: is_cvg_cst.
- rewrite Dopp; apply: is_cvgN; exact: is_cvg_cst.
  apply: cvgN; exact: cvg_at_right_filter.
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
  (* {within `]-oo, F a[, continuous G *)
  {in `]F a, +oo[, continuous G} ->
  (G x @[x --> (F a)^'+] --> G (F a)) ->
  F x @[x --> +oo%R] --> +oo%R ->
  {in `[F a, +oo[, forall x, (0 <= G x)%R} ->
  \int[mu]_(x in `[F a, +oo[) (G x)%:E =
  \int[mu]_(x in `[a, +oo[) (((G \o F) * F^`()) x)%:E.
Proof.
move=> incrF cF' /cvg_ex[/= r F'ar] /cvg_ex[/= l F'ool] cFa dF cG cGFa Fny G0.
transitivity (\int[mu]_(x in `[F a, +oo[) (((G \o -%R) \o -%R) x)%:E).
  by apply/eq_integral => x ? /=; rewrite opprK.
have cGN : {in `]-oo, - F a[%R, continuous (G \o -%R)}.
  move=> x; rewrite in_itv/= ltrNr => FaNx.
  apply: continuous_comp; first exact: continuousN.
  by apply: cG; rewrite in_itv/= FaNx.
rewrite -ge0_integration_by_substitution_oppr_oinfty_infty//; last 2 first.
- apply/cvg_at_rightNP.
  apply: cvg_toP; first by apply/cvg_ex; exists (G (F a)).
  by move/cvg_lim: cGFa => -> //; rewrite fctE opprK.
- by move=> x; rewrite in_itv/= lerNr => FaNx; apply: G0; rewrite in_itv/= FaNx.
rewrite (@ge0_integration_by_substitution_decreasing_opinfty (- F)%R); first last.
- move=> y.
  rewrite in_itv/= lerNr => FaNy.
  by apply: G0; rewrite in_itv/= FaNy.
- exact/cvgNrNy.
- rewrite fctE opprK.
  exact/cvg_at_rightNP.
- exact: cGN.
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

Lemma RintegralZl d (T : measurableType d) (R : realType)
  (mu : measure T R) (D : set T) :
  d.-measurable D ->
  forall (f : T -> R), mu.-integrable D (EFin \o f) ->
  forall r, (\int[mu]_(x in D) (r * f x) = r * \int[mu]_(x in D) f x)%R.
Proof.
move=> mD f intf r.
rewrite (_:r = fine r%:E)//.
rewrite -fineM//; last exact: integral_fune_fin_num.
congr (fine _).
under eq_integral do rewrite EFinM.
exact: integralZl.
Qed.

Lemma RintegralZr d (T : measurableType d) (R : realType)
  (mu : measure T R) (D : set T) :
  d.-measurable D ->
  forall (f : T -> R), mu.-integrable D (EFin \o f) ->
  forall r, (\int[mu]_(x in D) (f x * r) = \int[mu]_(x in D) f x * r)%R.
Proof.
move=> mD f intf r.
by rewrite mulrC -RintegralZl//; under eq_Rintegral do rewrite mulrC.
Qed.

Context {R : realType}.
Let mu := @lebesgue_measure R.

Lemma ge0_integralT_even (f : R -> R) :
  (forall x, (0 <= f x)%R) ->
  measurable_fun [set: R] f ->
  f =1 f \o -%R ->
    (\int[mu]_x (f x)%:E =
     2%:E * \int[mu]_(x in [set x | (0 <= x)%R]) (f x)%:E).
Proof.
move=> f0 mf evenf.
set posnums := [set x : R | (0 <= x)%R].
have mposnums : measurable posnums by rewrite /posnums -set_interval.set_itv_c_infty//.
rewrite -(setUv posnums).
rewrite ge0_integral_setU//= ; last 4 first.
- by apply: measurableC.
- apply/EFin_measurable_fun.
  by rewrite setUv.
  move=> x _.
  by rewrite lee_fin.
- exact/disj_setPCl.
rewrite mule_natl mule2n.
congr (_ + _).
rewrite /posnums.
rewrite -set_interval.set_itv_c_infty//.
rewrite set_interval.setCitvr.
(* rewrite integral_itv_bndo_bndc. *)
rewrite -set_interval.setU1itv//.
rewrite ge0_integral_setU//=; last 3 first.
- apply/EFin_measurable_fun.
  exact: measurable_funTS.
- by move=> x _; rewrite lee_fin.
- apply/disj_set2P.
  rewrite set1I ifF//.
  admit.
rewrite integral_set1 add0e.
rewrite -{1}oppr0.
rewrite integral_itv_obnd_cbnd; last admit.
rewrite integral_itv_bndo_bndc; last admit.
rewrite (@ge0_integration_by_substitution_decreasing_opinfty _ -%R f 0%R).
Abort.


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
Admitted.

End Rintegral_lemmas.

Section Gauss_integration.
Context {R : realType}.

(* TODO: PR *)
Lemma Rintegral_ge0 D (f : R -> R ) :
 (forall x, D x -> (0 <= f x)%R) -> (0 <= \int[lebesgue_measure]_(x in D) f x)%R.
Proof.
move=> f0.
rewrite fine_ge0//.
exact: integral_ge0.
Qed.

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
rewrite (ge0_within_pinfty_continuous_FTC2 _ cvgr_NexpR); last 6 first.
- by move=> x x0; rewrite expR_ge0.
- apply: cvg_at_right_filter.
  rewrite expRN.
  under eq_cvg do rewrite expRN.
  apply: cvgV; first by rewrite expR0.
  exact: continuous_expR.
- move=> x x0.
  apply: continuous_comp; first exact: opp_continuous.
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

Let oneDsqrx (x : R) := (1%R + (x ^+ 2)%R)%E.

Let gt0_oneDsqrx x : (0 < oneDsqrx x)%R.
Proof. by apply: ltr_wpDr => //; apply: sqr_ge0. Qed.

Let ge1_oneDsqrx x : (1%R <= oneDsqrx x)%R.
Proof. by rewrite lerDl; apply: sqr_ge0. Qed.

Let lt1_oneDsqrx x : (oneDsqrx\^-1 x <= 1%R)%R.
Proof. by rewrite invr_le1//; apply: unitf_gt0. Qed.

Let cVoneDsqrx : continuous (oneDsqrx\^-1)%R.
Proof.
move=> x.
apply: cvgV; first exact: lt0r_neq0.
apply: cvgD => //=; first exact: cvg_cst.
exact: sqr_continuous.
Qed.

Let even_oneDsqrx x : oneDsqrx x = oneDsqrx (- x).
Proof. by rewrite /oneDsqrx; congr +%R; rewrite !expr2 mulrN mulNr opprK. Qed.

Let dJ (x y : R) := (expR ((- x ^+ 2)%R * oneDsqrx y) / oneDsqrx y)%R.

Let J (x : R) := (\int[mu]_(y in `[0%R, +oo[) (dJ x y))%R.

Let fin_num_int_V1sqrx n : \int[@lebesgue_measure R]_(x in `[0%R, n%:R]) (oneDsqrx\^-1 x)%:E \is a fin_num.
Proof.
have int1_lty : \int[@lebesgue_measure R]_(_ in `[0%R, n%:R]) 1 < +oo.
  rewrite integral_cst//= mul1e lebesgue_measure_itv.
  by case: ifP => //= _; rewrite oppr0 adde0 ltey.
rewrite ge0_fin_numE; last first.
  by apply: integral_ge0 => x _; rewrite lee_fin invr_ge0 ltW.
apply: le_lt_trans int1_lty.
apply: ge0_le_integral => //=.
- by move=> x _; rewrite lee_fin invr_ge0 ltW.
- apply: measurableT_comp => //; apply: measurable_funTS.
  exact: continuous_measurable_fun.
- by move=> x _; rewrite lee_fin; move: (lt1_oneDsqrx x).
Qed.

Let datan : {in `]0%R, +oo[, (@atan R)^`() =1 oneDsqrx\^-1}.
Proof.
move=> x _.
rewrite derive1E.
apply: derive_val.
Qed.

Let J0E :
 \int[mu]_(y in `[0%R, +oo[) (dJ 0%R y)%:E = (@pi R / 2)%:E.
Proof.
rewrite /dJ expr0n/= oppr0.
under eq_integral do rewrite mul0r expR0 div1r.
rewrite (ge0_within_pinfty_continuous_FTC2 _ atan_pinfty_pi2)/=; last 6 first.
- by move=> x _; rewrite invr_ge0 ltW// gt0_oneDsqrx.
- by apply: cvg_at_right_filter; apply: cVoneDsqrx.
- by move=> x x0; apply: cVoneDsqrx.
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
apply: cvg_EFin; last exact: atan_pinfty_pi2.
near=> x.
rewrite ge0_fin_numE; last first. by rewrite lee_fin -atan0 nondecreasing_atan.
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
exact: continuous_measurable_fun.
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
    rewrite lee_fin divr_ge0//; first exact: expR_ge0.
    exact: ltW (gt0_oneDsqrx z).
  - exact: measurable_funTS (mdJ x).
  - move=> z _.
    by rewrite /dJ expr0n oppr0/= mul0r expR0 div1r lee_fin invr_ge0 ltW// gt0_oneDsqrx.
  - exact: measurable_funTS (mdJ 0%R).
  move=> z z0.
  rewrite lee_fin ler_pdivrMr; last exact (gt0_oneDsqrx z).
  rewrite divfK; last exact: lt0r_neq0 (gt0_oneDsqrx z).
  rewrite ler_expR expr0n oppr0/= mul0r pmulr_lle0.
    by rewrite lerNl oppr0 sqr_ge0.
  exact: gt0_oneDsqrx z.
by rewrite J0E ltey.
Qed.

Let eJoo : (J x)%:E @[x --> +oo%R] --> 0%:E.
Proof.
apply: cvg_EFin => //; first exact: nearW.
rewrite /J fctE/=.
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
      apply: divr_ge0; first exact: expR_ge0.
      exact: ltW (gt0_oneDsqrx _).
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
  rewrite lee_fin ler_pdivrMr; last exact: (gt0_oneDsqrx y).
  rewrite mulrA divfK; last exact: lt0r_neq0 (gt0_oneDsqrx y).
  rewrite expr0n oppr0/= mul0r expR0 mulr1 ler_expR.
  by rewrite ler_neMr//; rewrite oppr_le0; exact: sqr_ge0.
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

Local Import set_interval.
(* TODO: PR *)
Lemma continuous_within_itvcyP (* R : realType *) (a : R) (f : R -> R) :
  {within `[a, +oo[, continuous f} <->
  {in `]a, +oo[, continuous f} /\ f x @[x --> a^'+] --> f a.
Proof.
split=> [af|].
  have aa : a \in `[a, +oo[ by rewrite !in_itv/= lexx.
  split; [|apply/cvgrPdist_lt => eps eps_gt0 /=].
  - suff : {in `]a, +oo[%classic, continuous f}.
      by move=> P c W; apply: P; rewrite inE.
    rewrite -continuous_open_subspace; last exact: interval_open.
    move: af; apply/continuous_subspaceW.
    by move=> ?/=; rewrite !in_itv/= !andbT; exact: ltW.
  - move/continuous_withinNx/cvgrPdist_lt/(_ _ eps_gt0) : (af a).
    rewrite /dnbhs/= near_withinE near_simpl /prop_near1/nbhs/=.
    rewrite -nbhs_subspace_in// /within/= near_simpl.
    apply: filter_app; exists 2%R => //= c ca1 + ac.
    by apply; rewrite ?gt_eqF ?in_itv/= ?ltW.
move=> [cf fa].
apply/subspace_continuousP => x /andP[].
rewrite bnd_simp/= le_eqVlt => /predU1P[<-{x}|ax] _.
- apply/cvgrPdist_lt => eps eps_gt0/=.
  move/cvgrPdist_lt/(_ _ eps_gt0) : fa.
  rewrite /at_right !near_withinE.
  apply: filter_app; exists 1%R => //= c c1a + ac.
  rewrite in_itv/= andbT le_eqVlt in ac.
  by case/predU1P : ac => [->|/[swap]/[apply]//]; rewrite subrr normr0.
  have xaoo : x \in `]a, +oo[ by rewrite in_itv/= andbT.
  rewrite within_interior; first exact: cf.
  suff : `]a, +oo[ `<=` interior `[a, +oo[ by exact.
  rewrite -open_subsetE; last exact: interval_open.
  by move=> ?/=; rewrite !in_itv/= !andbT; exact: ltW.
Qed.

(* TODO: PR *)
Lemma continuous_within_itvycP (* R : realType *) (b : R) (f : R -> R) :
  {within `]-oo, b], continuous f} <->
  {in `]-oo, b[, continuous f} /\ f x @[x --> b^'-] --> f b.
Proof.
split=> [bf|].
  have bb : b \in `]-oo, b] by rewrite !in_itv/= lexx.
  split; [|apply/cvgrPdist_lt => eps eps_gt0 /=].
  - suff : {in `]-oo, b[%classic, continuous f}.
      by move=> P c W; apply: P; rewrite inE.
    rewrite -continuous_open_subspace; last exact: interval_open.
    move: bf; apply/continuous_subspaceW.
    by move=> ?/=; rewrite !in_itv/=; exact: ltW.
  - move/continuous_withinNx/cvgrPdist_lt/(_ _ eps_gt0) : (bf b).
    rewrite /dnbhs/= near_withinE near_simpl /prop_near1/nbhs/=.
    rewrite -nbhs_subspace_in// /within/= near_simpl.
    apply: filter_app; exists 1%R => //= c cb1 + bc.
    by apply; rewrite ?lt_eqF ?in_itv/= ?ltW.
move=> [cf fb].
apply/subspace_continuousP => x /andP[_].
rewrite bnd_simp/= le_eqVlt=> /predU1P[->{x}|xb].
- apply/cvgrPdist_lt => eps eps_gt0/=.
  move/cvgrPdist_lt/(_ _ eps_gt0) : fb.
  rewrite /at_right !near_withinE.
  apply: filter_app; exists 1%R => //= c c1b + cb.
  rewrite in_itv/= le_eqVlt in cb.
  by case/predU1P : cb => [->|/[swap]/[apply]//]; rewrite subrr normr0.
  have xb_i : x \in `]-oo, b[ by rewrite in_itv/=.
  rewrite within_interior; first exact: cf.
  suff : `]-oo, b[ `<=` interior `]-oo, b] by exact.
  rewrite -open_subsetE; last exact: interval_open.
  by move=> ?/=; rewrite !in_itv/=; exact: ltW.
Qed.

Lemma ge0_integrable_comp_continuous_increasing (f g : R -> R)
 (l : R) (ir : itv_bound R) :
  let i := Interval (BLeft l) ir in
  {within [set` i], continuous f} ->
  {in [set` i], {homo f : x y / (x < y)%R}} ->
  {in [set` i], forall x, (0 <= g x)%R} ->
  mu.-integrable [set` i] (EFin \o g) ->
  mu.-integrable [set` i] (EFin \o (g \o f)).
Proof.
Admitted.

Let dJE : {in `]0%R, +oo[, J^`() =1 (fun x => (- 2) * Ig * (gauss x))%R}.
Proof.
move=> x; rewrite in_itv/= => /andP[x0 _].
pose d_dx_dJ x0 y0 :=(dJ^~ y0)^`() x0.
rewrite /J.
(* interchange integration and derivation *)
(* by lebesgue differentiaton theorem? *)
(* FTC1 *)
transitivity ((\int[mu]_(y in `[0, +oo[) d_dx_dJ x y)%R).
  admit.
have substE : \int[mu]_(y in `[0%R, +oo[) (expR (- x ^+ 2 * oneDsqrx y))%:E =
  \int[mu]_(y in `[0%R, +oo[)
                    ((((fun z => expR (- x ^+ 2) / x * expR (- z ^+ 2)) \o
                    (fun z => x * z)) * (fun z => x * z)^`()) y)%:E.
  apply: eq_integral => y _.
  rewrite !fctE derive1E.
  rewrite derive_val /GRing.scale/= mulr1.
  rewrite mulrAC divfK//; last by rewrite gt_eqF.
  by rewrite mulrDr mulr1 mulNr -exprMn expRD.
transitivity (-2 * x * \int[mu]_(y in `[0, +oo[) (expR ((- x ^+ 2) * oneDsqrx y)))%R.
  rewrite /Rintegral (_:-2 * x = fine (-2 * x)%:E)%R//.
  rewrite -fineM; last 2 first.
  - rewrite le0_fin_numE ?ltNyr//.
    rewrite lee_fin.
    by rewrite mulr_le0_ge0// ltW.
  - rewrite ge0_fin_numE; last first.
      admit.
    rewrite substE.
    rewrite -ge0_integration_by_substitution_increasing_opinfty; first last.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    rewrite mulr0.
    rewrite (@itv_bndbnd_setU _ _ _ (BLeft 1%R))//; last by rewrite bnd_simp.
    rewrite ge0_integral_setU//=; first last.
    - admit.
    - admit.
    - admit.
    under eq_integral do rewrite EFinM.
    rewrite ge0_integralZl//; first last.
    - admit.
    - move=> ? _; exact: expR_ge0.
    - admit.
    apply: lte_add_pinfty.
    apply: lte_mul_pinfty.
    - admit.
    - admit.
    admit.
    apply: (@le_lt_trans _ _ Ig%:E).
      admit.
    exact: ltry.
  rewrite mulNr EFinN mulNe.
  rewrite -ge0_integralZl//; first last.
  - admit.
  - admit.
  - admit.
  rewrite -integral_ge0N; last first.
    admit.
  congr fine.
  apply: eq_integral=> y; rewrite inE/= in_itv/= => y0.
  rewrite /d_dx_dJ derive1E.
  rewrite /dJ; under eq_fun do (rewrite mulrC); rewrite deriveZ/=; last exact: ex_derive.
  rewrite -derive1E derive1_comp; first last.
  - admit.
  - admit.
  rewrite derive1E derive_val.
  rewrite mulrC /GRing.scale/= mulrA.
  under eq_fun do (rewrite mulrC); rewrite derive1E deriveZ/=; last exact: ex_derive.
  rewrite mulrA mulVf ?mul1r; last rewrite gt_eqF//.
  rewrite deriveN// mulNr; congr (- _%:E).
  rewrite exp_derive expr1.
  by rewrite /GRing.scale/= mulr1.
rewrite /Rintegral substE.
rewrite -ge0_integration_by_substitution_increasing_opinfty//; first last.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
rewrite mulr0.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl//=; first last.
- admit.
- admit.
- admit.
rewrite fineM/=; first last.
- admit.
- admit.
rewrite -!mulrA.
rewrite [X in (-2 * X)%R]mulrCA !mulrA mulfK; last first.
  admit.
by rewrite mulrAC.
Admitted.

(* ref: https://www.phys.uconn.edu/~rozman/Courses/P2400_17S/downloads/gaussian-integral.pdf *)
Lemma gauss_integration : (\int[mu]_x (gauss x))%R = Num.sqrt pi.
Proof.
have -> : (\int[mu]_x gauss x)%R = (Ig * 2)%R.
  rewrite Rintegral_even//=; last 2 first.
  - rewrite eqEsubset; split => x//=.
    by move=> _; exists (- x)%R => //; rewrite opprK.
  - move=> x.
    by rewrite /gauss sqrrN.
  rewrite [RHS]mulrC; congr (2%R * _)%R.
  by rewrite [X in (\int[_]_(_ in X) _)%R](_:_= `[0%R, +oo[%classic).
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
rewrite -(le0_within_pinfty_continuous_FTC2 _ eJoo _ _ _ dJE); last 4 first.
- move=> x x0.
  rewrite -mulN1r -!mulrA mulN1r.
  rewrite lerNl oppr0 pmulr_rge0//.
  apply: mulr_ge0 => //.
  exact: Rintegral_ge0.
- apply: cvg_at_right_filter; exact: cdJ.
- move=> x _; exact: cdJ.
- by move=> x x0.
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
Qed.

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
