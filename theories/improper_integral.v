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

Lemma cvg_expR {R : realType} :
  @expR R (1%R *- n) @[n --> \oo] --> 0%R.
Proof.
Admitted.

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
  ereal_sup [set (\int[lebesgue_measure]_(x in (S i)) f x) | i in [set: nat] ] =
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
  exact: emeasurable_funN.
move=> x Sx.
rewrite leeNr oppe0.
exact: f0.
Admitted.

Lemma ge0_within_pinfty_continuous_FTC2 {R : realType} (f F : R -> R) a (l : \bar R) :
  (forall x, (a < x)%R -> 0 <= f x)%R ->
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

Lemma le0_within_pinfty_continuous_FTC2 {R : realType} (f F : R -> R) a (l : \bar R) :
  (forall x, (a < x)%R -> f x <= 0)%R ->
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
exact: cvg_expR.
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

Lemma Rintegral_even D (f : R -> R) :
  (D = -%R @` D) ->
  (forall x, f x = f (- x)%R) ->
  (\int[lebesgue_measure]_(x in D) f x =
     \int[lebesgue_measure]_(x in [set x | D x /\ (0 <= x)%R]) f x)%R.
Proof.
Admitted.

(* TODO: PR *)
Lemma increasing_atan : {homo (@atan R) : x y / (x < y)%R}.
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

(* TODO: PR *)
Lemma atan_pinfty_pi2 : (@atan R) x @[x --> +oo%R] --> pi / 2.
Proof.
rewrite (_: pi / 2 = sup (range atan)); last first.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - have -> : (@pi R / 2)%R = sup `[0%R, pi / 2[%classic.
      rewrite real_interval.sup_itv// bnd_simp.
      by have /andP[] := pihalf_02 R.
    apply: le_sup; last 2 first.
        exists 0%R.
        rewrite /= in_itv/= lexx/=.
        by have /andP[] := pihalf_02 R.
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
    by have /andP[] := pihalf_02 R.
  - apply: sup_le_ub.
      by exists 0%R; exists 0%R => //; apply: atan0.
    move=> _ /= [x _ <-].
    by apply: ltW; apply: atan_ltpi2.
apply: nondecreasing_cvgr.
move=> x y.
rewrite le_eqVlt => /predU1P[-> //|xy].
  by apply: ltW; apply: increasing_atan.
exists (pi / 2)%R.
move=> _ /= [x _ <-].
by apply: ltW; apply: atan_ltpi2.
Qed.

Local Import Num.

Definition gauss := (fun x : R => expR (- (x ^ 2)))%R.
Let mu := @lebesgue_measure R.
Let Ig := (\int[mu]_(x in `[0%R, +oo[) gauss x)%R.

Let J (x : R) := (\int[mu]_(y in `[0%R, +oo[)
  (fun y => expR (- (x ^+ 2 * (1 + y ^+ 2))) / (1 + y ^+ 2)) y)%R.

(* ref: https://www.phys.uconn.edu/~rozman/Courses/P2400_17S/downloads/gaussian-integral.pdf *)
Lemma gauss_integration : (\int[mu]_x (gauss x))%R = sqrt pi.
Proof.
have -> : (\int[mu]_x gauss x)%R = (2 * Ig)%R.
  rewrite Rintegral_even/=; last 2 first.
      admit.
    admit.
  admit.
rewrite -[RHS](@divfK _ 2)//.
rewrite [LHS]mulrC.
congr (_ * 2)%R.
have gauss_ge0 (x : R) : (0 <= gauss x)%R by exact: expR_ge0.
have J0 : (atan x)%:E @[x --> +oo%R] --> (J 0)%:E.
  admit.
have Joo : J x @[x --> +oo%R] --> 0%R.
  admit.
have dJ : {in `]0%R, +oo[, J^`() =1 (fun x => (- 2) * Ig)%R}.
  admit.
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
transitivity (J 0 / 2)%R; last first.
  congr (_ / 2)%R.
  rewrite /J.
  under eq_Rintegral do rewrite expr0n/= mul0r oppr0 expR0.
  have datan : {in `]0%R, +oo[, (@atan R)^`() =1 (fun x => 1 / (1%R + (x ^+ 2)%R)%E)}.
    move=> x _.
    rewrite derive1E.
    apply: derive_val.
    rewrite div1r.
    exact: is_derive1_atan.
  rewrite (_:(pi / 2) = fine ((pi / 2)%:E)); last by [].
  congr (fine _).
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
apply: (@mulIf _ (- 2)%R) => //.
rewrite !mulrN divfK//.
apply/esym.
(* lemma? *)
have EFinK (x : R) : x = fine (EFin x) by [].
rewrite -[LHS]add0r [LHS]EFinK.
rewrite [RHS]EFinK.
congr (fine _).
have eJoo : (J x)%:E @[x --> +oo%R] --> 0%:E.
  apply: cvg_EFin => //.
  exact: nearW.
rewrite EFinB.
rewrite -(le0_within_pinfty_continuous_FTC2 _ eJoo _ _ _ dJ); last 4 first.
- move=> x x0.
  rewrite -mulN1r -mulrA mulN1r.
  rewrite lerNl oppr0 pmulr_rge0//.
  exact: Rintegral_ge0.
- exact: cvg_cst.
- by move=> x x0; apply: cvg_cst.
- by move=> x x0; apply: derivable_cst.
under eq_integral.
  move=> x _.
  rewrite -mulN1r -mulrA mulN1r.
  rewrite (_: _%:E = (- (cst (2 * Ig))%R x).

xxx
(*
    have cvg_pi2x: ((@pi R) / 2 - x^-1)%:E @[x --> +oo%R] --> (pi / 2)%:E.
      apply: cvg_EFin.
        exact: nearW.
      rewrite -[X in _ --> X]subr0.
      apply: cvgB; first exact: cvg_cst.
      apply/cvgrVy.
        near=> a.
        rewrite invr_gt0.
        near: a.
        exact: nbhs_pinfty_gt.
      under eq_cvg do rewrite /=invrK.
      exact: cvg_id.
*)
    
      
(* cos_atan *)
Admitted.

End Gauss_integration.
