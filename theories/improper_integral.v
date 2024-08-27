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

Lemma ge0_within_pinfty_continuous_FTC2 {R : realType} (f F : R -> R) a (l : \bar R) :
  (forall x, 0 <= f x)%R ->
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
      (* applying improper_integral *)
      rewrite -ge0_nondecreasing_set_cvg_integral//; last 3 first.
          apply/nondecreasing_seqP => n.
          rewrite subsetEset => x/=.
          rewrite !in_itv/= => /andP[-> xnS]/=.
          apply: (le_trans xnS).
          by rewrite ler_nat.
        apply: measurable_funTS.
        apply: (measurable_comp measurableT) => //.
        exact: (measurable_comp measurableT).
      by move=> ? _; apply: expR_ge0.
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
have J0 : atan x @[x --> +oo%R] --> J 0.
  admit.
have Joo : J x @[x --> +oo%R] --> 0%R.
  admit.
have dJ : J^`() =1 (fun x => (- 2) * expR (- x ^+ 2))%R.
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
    
  rewrite within_pinfty_continuous_FTC2.

  
rewrite -(_: 
ewrite 
(* cos_atan *)
Admitted.

End Gauss_integration.
