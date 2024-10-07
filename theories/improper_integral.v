Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum exp.
Require Import measure lebesgue_measure numfun lebesgue_integral itv.
Require Import realfun derive.
Require Import trigo.


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

(* from PR#1266 *)
Section integration_by_parts.
Context {R : realType}.
Notation mu := lebesgue_measure.
Local Open Scope ereal_scope.
Implicit Types (F G f g : R -> R) (a b : R).

Lemma continuous_integration_by_parts F G f g a b :
    (a < b)%R ->
    {in `[a, b], continuous f} -> {in `[a, b], continuous F} ->
    derivable_oo_continuous_bnd F a b ->
    {in `]a, b[, F^`() =1 f} ->
    {in `[a, b], continuous g} -> {in `[a, b], continuous G} ->
    derivable_oo_continuous_bnd G a b ->
    {in `]a, b[, G^`() =1 g} ->
  (\int[mu]_(x in `[a, b]) (F x * g x)%:E = (F b * G b - F a * G a)%:E -
   \int[mu]_(x in `[a, b]) (f x * G x)%:E).
Proof.
Admitted.

End integration_by_parts.

(* PR #1266 *)
Section FTC2.
Context {R : realType}.
Notation mu := lebesgue_measure.
Local Open Scope ereal_scope.
Implicit Types (f F : R -> R) (a b : R). 

Corollary within_continuous_FTC2 f F a b : (a < b)%R ->
  {within `[a, b], continuous f} ->
  derivable_oo_continuous_bnd F a b ->
  {in `]a, b[, F^`() =1 f} ->
  (\int[mu]_(x in `[a, b]) (f x)%:E = (F b)%:E - (F a)%:E)%E.
Proof. Admitted.


End FTC2.

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

Lemma cvgn_expR {R : realType} :
  @expR R (1%R *- n) @[n --> \oo] --> 0%R.
Proof.
under eq_cvg do rewrite -mulNrn -mulr_natr expRM_natr.
apply: cvg_expr.
rewrite expRN ger0_norm.
  rewrite invf_lt1 => //.
    by rewrite expR_gt1.
  by rewrite expR_gt0.
by rewrite invr_ge0 expR_ge0.
Qed.

Lemma cvgr_expR {R: realType} :
  (@expR R (- x)) @[x --> +oo%R] --> 0%R.
Proof.
apply/cvgrPdist_le => e e0.
near=> x.
rewrite sub0r normrN ger0_norm; last exact: expR_ge0.
rewrite expRN -[leRHS]invrK lef_pV2; last 2 first.
    by rewrite posrE; apply: expR_gt0.
  by rewrite posrE invr_gt0.
apply: le_trans (expR_ge1Dx _) => //.
rewrite -lerBlDl.
near: x.
apply: nbhs_pinfty_ge.
exact: num_real.
Unshelve. end_near. Qed.

Section within_continuous_FTC2_pinfty.

Lemma ge0_nondecreasing_set_cvg_integral {R : realType}
  (S : nat -> set R) (f : R -> \bar R) :
   {homo S : n m / (n <= m)%N >-> (n <= m)%O} ->
  (forall i, measurable (S i)) ->
  measurable (\bigcup_i S i) ->
  measurable_fun (\bigcup_i S i) f ->
  (forall x, (\bigcup_i S i) x -> 0 <= f x) ->
  ereal_sup [set (\int[lebesgue_measure]_(x in (S i)) f x) | i in [set: nat] ] =
     \int[lebesgue_measure]_(x in \bigcup_i S i) f x.
Proof.
move=> nndS mS mUS mf f0.
apply/esym.
have : \int[lebesgue_measure]_(x in S i) f x @[i --> \oo] -->
   ereal_sup [set \int[lebesgue_measure]_(x in S i) f x | i in [set: nat]].
  apply: (@ereal_nondecreasing_cvgn _ (fun i => \int[lebesgue_measure]_(x in S i) f x)).
  apply/nondecreasing_seqP => n.
  apply: ge0_subset_integral => /=.
          exact: mS.
        exact: mS.
      apply: measurable_funS mf.
        exact: mUS.
      exact: bigcup_sup.
    move=> x Snx.
    apply: f0.
    by exists n.+1.
  rewrite -subsetEset.
  exact: nndS.
move/cvg_lim => <- //.
apply/esym.
under eq_fun do rewrite integral_mkcond/=.
rewrite -monotone_convergence//=; last 3 first.
      move=> n.
      apply/(measurable_restrictT f) => //.
      apply: measurable_funS mf => //.
      exact: bigcup_sup.
    move=> n x _.
    apply: erestrict_ge0 => {}x Snx.
    apply: f0.
    by exists n.
  move=> x _.
  apply/nondecreasing_seqP => n.
    apply: restrict_lee => //.
    move=> {}x Snx.
    apply: f0.
    by exists n.+1.
  rewrite -subsetEset.
  exact: nndS.
rewrite [RHS]integral_mkcond/=.
apply: eq_integral => /=.
rewrite /g_sigma_algebraType/ocitv_type => x _.
transitivity (ereal_sup (range (fun x0 : nat => (f \_ (S x0)) x))).
  apply/cvg_lim => //.
  apply: ereal_nondecreasing_cvgn.
  apply/nondecreasing_seqP => n.
  apply: restrict_lee.
    move=> {}x Snx.
    apply: f0.
    by exists n.+1.
  rewrite -subsetEset.
  exact: nndS.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: ub_ereal_sup.
  move=> _/= [n _ <-].
  apply: restrict_lee => //.
  exact: bigcup_sup.
- rewrite patchE.
  case: ifP.
    rewrite inE.
    move=> [n _ Snx].
    apply: ereal_sup_le.
    exists ((f \_ (S n)) x) => //.
    rewrite patchE ifT=> //.
    by rewrite inE.
  move/negbT/negP.
  rewrite inE /bigcup/=.
  move/forallPNP => nSx.
  apply/ereal_sup_le.
  exists point => //.
  exists 0%R => //.
  rewrite patchE ifF//.
  apply/negbTE.
  apply/negP.
  rewrite inE.
  exact: nSx.
Qed.

Lemma le0_nondecreasing_set_cvg_integral {R : realType}
  (S : nat -> set R) (f : R -> \bar R) :
   {homo S : n m / (n <= m)%N >-> (n <= m)%O} ->
  (forall i, measurable (S i)) ->
  measurable (\bigcup_i S i) ->
  measurable_fun (\bigcup_i S i) f ->
  (forall x, (\bigcup_i S i) x -> f x <= 0) ->
  ereal_inf [set (\int[lebesgue_measure]_(x in (S i)) f x) | i in [set: nat] ] =
     \int[lebesgue_measure]_(x in \bigcup_i S i) f x.
Proof.
move=> incrS mS mUS mf f0.
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
move=> f_ge0 Fxl fa cf dF Fa dFE.
rewrite -integral_itv_obnd_cbnd; last first.
  apply: open_continuous_measurable_fun.
    exact: interval_open.
  move=> x; rewrite inE/= in_itv/= => /andP[ax _].
  exact: cf.
rewrite itv_bnd_infty_bigcup.
rewrite seqDU_bigcup_eq.
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
admit.
  apply: eq_eseriesr => n _.
  rewrite (_: seqDU (fun k : nat => `]a, (a + k%:R)]%classic) n.+1 = `](a + n%:R), (a + n.+1%:R)]%classic).
rewrite integral_itv_obnd_cbnd; last first.
  admit.
have dFEn : {in `]a + n%:R, a + n.+1%:R[, F^`() =1 f}.
  admit.
rewrite (within_continuous_FTC2 _ _ _ dFEn)//.
- admit.
- admit.
- admit.
rewrite /seqDU.
admit.
rewrite increasing_telescope_sume_infty_fin_num; last 2 first.
    admit.
  admit.
rewrite addr0 EFinN; congr (_ - _).
apply/cvg_lim => //.
have -> : l%:E = ereal_sup (range (fun n => (F (a + n%:R))%:E)).
  admit.
apply: ereal_nondecreasing_cvgn.
admit.
Admitted.

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
      rewrite -ge0_nondecreasing_set_cvg_integral//; last 3 first.
            exact: bigcupT_measurable.
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
  rewrite (@within_continuous_FTC2 _ (fun x => expR (- x)) (fun x => - expR (- x))%R 0%R n.+1%:R)//; last 3 first.
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

Lemma Rintegral_even (D : set R) (f : R -> R) :
  (D = -%R @` D) ->
  (forall x, f x = f (- x)%R) ->
  (\int[lebesgue_measure]_(x in D) f x =
     2 * \int[lebesgue_measure]_(x in [set x | D x /\ (0 <= x)%R]) f x)%R.
Proof.
pose Dp := [set x : R | (x \in D) /\ (0 <= x)%R].

Admitted.

(* TODO: rename *)
Lemma homo_lt_atan : {homo (@atan R) : x y / (x < y)%R}.
Proof.
move=> x y xy.
rewrite -subr_gt0.
have datan z : z \in `]x, y[ -> is_derive z 1%R atan (1 + z ^+ 2)^-1.
  move=> _; exact: is_derive1_atan.
have catan : {within `[x, y], continuous atan}.
  apply: derivable_within_continuous => z _.
  exact: ex_derive.
have := (MVT xy datan catan).
move=> [] c.
case : (@eqVneq _ c 0%R) => [-> _| c0 _] ->.
  by rewrite expr0n/= addr0 invr1 mul1r subr_gt0.
rewrite pmulr_lgt0; last by rewrite subr_gt0.
rewrite invr_gt0.
apply: addr_gt0 => //.
rewrite expr2.
move : c0.
case : (ltP 0%R c) => [c0 nc0|]; first exact: mulr_gt0.
rewrite le_eqVlt => /predU1P[->/negP//|c0 _].
by rewrite nmulr_rgt0.
Qed.

Lemma nondecreasing_atan : {homo @atan R : x y / (x <= y)%R}.
Proof.
move=> x y.
rewrite le_eqVlt => /predU1P[-> //|xy].
apply: ltW.
exact: homo_lt_atan.
Qed.

(* TODO: PR *)
Lemma atan_pinfty_pi2 : (@atan R) x @[x --> +oo%R] --> pi / 2.
Proof.
rewrite (_: pi / 2 = sup (range atan)); last first.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - have -> : (@pi R / 2)%R = sup `[0%R, pi / 2[%classic.
      rewrite real_interval.sup_itv// bnd_simp.
      exact: lt_le_trans (pihalf_ge1 _).
    apply: le_sup; last 2 first.
        exists 0%R.
        rewrite /= in_itv/= lexx/=.
        exact: lt_le_trans (pihalf_ge1 _).
      split.
        by exists 0%R; exists 0%R => //; rewrite atan0.
      exists (pi / 2)%R.
      move=> _ [x _ <-].
      by rewrite ltW// atan_ltpi2.
    move=> x/=.
    rewrite in_itv/= => /andP[x0 xpi2].
    apply/downP.
    exists (atan (tan x)) => /=.
      by exists (tan x).
    rewrite tanK//.
    rewrite in_itv/= xpi2 andbT.
    apply: lt_le_trans x0.
    rewrite ltrNl oppr0.
    exact: lt_le_trans (pihalf_ge1 _).
  - apply: sup_le_ub.
      by exists 0%R; exists 0%R => //; apply: atan0.
    move=> _ /= [x _ <-].
    by apply: ltW; apply: atan_ltpi2.
apply: (nondecreasing_cvgr nondecreasing_atan).
exists (pi / 2)%R.
move=> _ /= [x _ <-].
by apply: ltW; apply: atan_ltpi2.
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

Let J (x : R) := (\int[mu]_(y in `[0%R, +oo[)
  (fun y => expR (- (x ^+ 2 * (1 + y ^+ 2))) / (1 + y ^+ 2)) y)%R.

Let dJ0 (x : R) := (1 / (1 + x ^+ 2))%R.

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


Let datan : {in `]0%R, +oo[, (@atan R)^`() =1 (fun x => 1 / (1%R + (x ^+ 2)%R)%E)}.
Proof.
move=> x _.
rewrite derive1E.
apply: derive_val.
rewrite div1r.
exact: is_derive1_atan.
Qed.

Let J0E :
 \int[mu]_(y in `[0%R, +oo[) (expR (- (0%R ^+ 2 * (1%R + (y ^+ 2)%R)%E))
           / (1%R + (y ^+ 2)%R)%E)%:E = (@pi R / 2)%:E.
Proof.
rewrite /J expr0n/=.
under eq_integral do rewrite mul0r oppr0 expR0 div1r.
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

Let mJ r : measurable_fun setT (fun y : R =>
        (expR (- (r ^+ 2 * (1%R + (y ^+ 2)%R)%E)) / (1%R + (y ^+ 2)%R)%E)%:E).
Proof.
apply: measurableT_comp => //.
rewrite -mulrfctE.
apply: measurable_funM.
  apply: measurableT_comp => //.
  apply: measurableT_comp => //.
  apply: measurableT_comp => //.
  apply: continuous_measurable_fun.
  move=> x.
  apply: cvgD; first exact: cvg_cst.
  exact: sqr_continuous.
exact: continuous_measurable_fun.
Qed.

Let int_J z : mu.-integrable `[0%R, +oo[ (fun x : R =>
    (expR (- (z ^+ 2 * (1%R + (x ^+ 2)%R)%E)) / (1%R + (x ^+ 2)%R)%E)%:E).
Proof.
apply/integrableP; split; first exact: measurable_funTS (mJ z).
apply/abse_integralP => //; first exact: measurable_funTS (mJ z).
rewrite -fin_num_abs ge0_fin_numE; last first.
  apply: integral_ge0 => x x0.
  rewrite lee_fin divr_ge0//; first exact: expR_ge0.
  apply: addr_ge0 => //.
  exact: sqr_ge0.
apply: (@le_lt_trans _ _ (\int[mu]_(y in `[0%R, +oo[)
           (expR (- (0 ^+ 2 * (1%R + (y ^+ 2)%R)%E)) / (1%R + (y ^+ 2)%R)%E)%:E)).
  apply: ge0_le_integral => //.
  - move=> x _.
    rewrite lee_fin divr_ge0//; first exact: expR_ge0.
    exact: ltW (gt0_oneDsqrx x).
  - exact: measurable_funTS (mJ z).
  - move=> x _.
    by rewrite expr0n mul0r oppr0 expR0 div1r lee_fin invr_ge0 ltW// gt0_oneDsqrx.
  - exact: measurable_funTS (mJ 0%R).
  move=> x x0.
  rewrite lee_fin ler_pdivrMr; last exact (gt0_oneDsqrx x).
  rewrite divfK; last exact: lt0r_neq0 (gt0_oneDsqrx x).
  rewrite ler_expR expr0n mul0r lerN2 mulr_ge0//; first exact: sqr_ge0.
  exact: ltW (gt0_oneDsqrx x).
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
  rewrite -integralZl => //.
  apply: fine_le.
  - move: (int_J x).
    (* lemma? *)
    have J_ge0 : 0%R <=
      \int[mu]_(x0 in `[0%R, +oo[)
       (expR (- (x ^+ 2 * (1%R + (x0 ^+ 2)%R)%E)) / (1%R + (x0 ^+ 2)%R)%E)%:E.
      apply: integral_ge0 => y _.
      apply: divr_ge0; first exact: expR_ge0.
      exact: ltW (gt0_oneDsqrx _).
    move/integrableP => [_].
    rewrite ge0_fin_numE => //.
    move/(abse_integralP mu (measurable_itv _) (measurable_funTS (mJ _))).
    by rewrite -(@ge0_fin_numE _ (`| _|))// abse_fin_num ge0_fin_numE.
  - rewrite integralZl => //.
    apply: fin_numM => //.
    by rewrite J0E.
  apply: le_integral => //.
    by rewrite integrableZl.
  move=> y _.
  rewrite lee_fin ler_pdivrMr; last exact: (gt0_oneDsqrx y).
  rewrite mulrA divfK; last exact: lt0r_neq0 (gt0_oneDsqrx y).
  rewrite expr0n mul0r oppr0 expR0 mulr1 ler_expR lerN2.
  rewrite ler_peMr//; first exact: sqr_ge0.
  exact: ge1_oneDsqrx.
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

Let dJ : {in `]0%R, +oo[, J^`() =1 (fun x => (- 2) * Ig * (gauss x))%R}.
Proof.
move=> x; rewrite in_itv/= => /andP[x0 _].
have -> : J ^`() x = (\int[mu]_(y in `[0%R, +oo[)
    (fun y0 : R => (fun x => expR (- (x ^+ 2 * (1%R + (y0 ^+ 2)%R)%E))
         / (1%R + (y0 ^+ 2)%R)%E)^`() x) y)%R.
(* interchange integration and derivation *)
(* by lebesgue differentiaton theorem? *)
  admit.
under eq_Rintegral => y _.
  rewrite derive1E deriveM//=.
  rewrite -!derive1E derive1_cst scaler0 add0r.
  rewrite derive1_comp//.
  rewrite !derive1E.
  have /funeqP /(_ (- (x ^+ 2 * (1%R + (y ^+ 2))))%R) -> := derive_expR R.
  rewrite deriveN// deriveM//.
  rewrite -derive1E derive1_cst scaler0 add0r (deriveX 1%R)//.
  rewrite (@derive_val _ _ _ _ _ _ _ (is_derive_id x 1%R)).
  rewrite expr1.
  
  admit.
Admitted.

(* ref: https://www.phys.uconn.edu/~rozman/Courses/P2400_17S/downloads/gaussian-integral.pdf *)
Lemma gauss_integration : (\int[mu]_x (gauss x))%R = sqrt pi.
Proof.
have -> : (\int[mu]_x gauss x)%R = (Ig * 2)%R.
  rewrite Rintegral_even/=; last 2 first.
      rewrite eqEsubset; split => x//=.
      by move=> _; exists (- x)%R => //; rewrite opprK.
    move=> x.
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
rewrite -(le0_within_pinfty_continuous_FTC2 _ eJoo _ _ _ dJ); last 4 first.
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