(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval poly.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions reals interval_inference topology.
From mathcomp Require Import prodnormedzmodule tvs normedtype landau forms.
From mathcomp Require Import sequences derive measure lebesgue_measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral ereal ftc.

(**md**************************************************************************)
(* # ODE                                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section setInterval.
Context {R : realType}.

Definition itv_bound_swap (i : interval R) :=
match i.1 with
| BSide b0 x =>
  match i.2 with
  | BSide b1 y => (Interval (BSide b0 y) (BSide b1 x))
  | BInfty b1 => (Interval (@BInfty _ b1) (BSide b1 x))
  end
| BInfty b0 =>
  match i.2 with
  | BSide b1 y => (Interval (BSide b0 y) (@BInfty _ b0))
  | BInfty b1 => (Interval (@BInfty _ b1) (@BInfty _ b0))
  end
end.

Definition setInterval (i : interval R) :=
  [set` i] `|` [set` itv_bound_swap i].

Lemma setInterval_le (i : interval R) :
  (i.1 <= i.2)%O ->
  setInterval i = [set` i].
Proof.
rewrite /setInterval.
case i => /=.
case=> [b0 x|b0]; case=> [b1 y|b1]; case: b0; case: b1.
all: rewrite bnd_simp /itv_bound_swap.
all: rewrite ?set_itvxx ?set_itv_ybnd ?set_itv_bndNy ?setU0//=.
- move=> xy; suff : `[y, x[ = set0 by (move=> ->; rewrite setU0).
  by rewrite set_itv_ge ?bnd_simp ?le_gtF.
- rewrite le_eqVlt => /predU1P[<- |xy].
    by rewrite set_itv1 setUid.
  suff : `[y, x] = set0 by (move=> ->; rewrite setU0).
  by rewrite set_itv_ge ?bnd_simp ?lt_geF.
- move=> xy; suff : `]y, x[ = set0 by (move=> ->; rewrite setU0).
  by rewrite set_itv_ge ?bnd_simp ?le_gtF ?ltW.
- move=> xy; suff : `]y, x] = set0 by (move=> ->; rewrite setU0).
  by rewrite set_itv_ge ?bnd_simp ?le_gtF.
Qed.

Lemma setInterval_ge (i : interval R) :
  (i.2 <= i.1)%O ->
  setInterval i = [set` itv_bound_swap i].
Proof.
rewrite /setInterval.
case i => /=.
case=> [b0 x|b0]; case=> [b1 y|b1]; case: b0; case: b1.
all: rewrite bnd_simp /itv_bound_swap.
all: rewrite ?set_itvxx ?set_itv_ybnd ?set_itv_bndNy ?set0U//=.
- move=> yx; suff : `[x, y[ = set0 by (move=> ->; rewrite set0U).
  by rewrite set_itv_ge ?bnd_simp ?le_gtF.
- move=> yx; suff : `[x, y] = set0 by (move=> ->; rewrite set0U).
  by rewrite set_itv_ge ?bnd_simp ?lt_geF.
- move=> yx; suff : `]x, y[ = set0 by (move=> ->; rewrite set0U).
  by rewrite set_itv_ge ?bnd_simp ?le_gtF.
- move=> yx; suff : `]x, y] = set0 by (move=> ->; rewrite set0U).
  by rewrite set_itv_ge ?bnd_simp ?le_gtF.
Qed.

End setInterval.

(*
Notation "`[| x , y |]" := (setInterval (Interval (BLeft x) (BRight y))).
Notation "`]| x , y |[" := (setInterval (Interval (BRight x) (BLeft y))).

Section inteitv.
Local Open Scope ereal_scope.

Context {R : realType}.
Let mu := (@lebesgue_measure R).

Definition inteitv (a b : R) f :=
  if (a < b)%R then \int[mu]_(x in `[a, b]) f x
               else - \int[mu]_(x in `[b, a]) f x.

Definition derivable_oo_within_continuous (f : R -> R) a b :=
  {in `]|a, b|[, forall x : R, derivable f x 1} /\
  {within `[|a, b|], continuous f}.

Lemma continuous_FTC2_inteitv (f F : R -> R) a b :
  {within `[|a, b|], continuous f} ->
  derivable_oo_within_continuous F a b -> (* not derivable_oo_continuous_bnd *)
  {in `]|a, b|[%R, F^`()%classic =1 f} ->
  inteitv a b (EFin \o f) = (F b)%:E - (F a)%:E.
Proof.
have [] := ltP a b.
  move=> ab.
  rewrite setInterval_le ?bnd_simp ?ltW// => cf.
  move=> [].
  rewrite setInterval_le ?bnd_simp// => dF.
  rewrite setInterval_le ?bnd_simp ?ltW//.
  move/continuous_within_itvP => -[] // _ Fa Fb dFf.
  rewrite /inteitv ab.
  rewrite (@continuous_FTC2 _ f F)//.
    by split => // x xab; apply: dF; rewrite inE/=.
  by move=> x xab; apply: dFf; rewrite inE/=.
rewrite le_eqVlt => /predU1P[-> |ba].
  by rewrite /inteitv ltxx set_itv1 integral_set1 oppe0 subee.
rewrite setInterval_ge ?bnd_simp// => cf.
move=> [].
rewrite setInterval_ge ?bnd_simp ?ltW// => dF.
rewrite setInterval_ge ?bnd_simp//.
move/continuous_within_itvP => -[] // _ Fa Fb dFf.
rewrite /inteitv ifF; last first.
  by apply/negP/negP; rewrite le_gtF ?ltW.
rewrite (@continuous_FTC2 _ f F)// ?oppeB 1?addeC//.
  by split => // x xab; apply: dF; rewrite inE/=.
by move=> x xab; apply: dFf; rewrite inE/=.
Qed.

End inteitv.

Reserved Notation "\int [ mu ]_( x $ a ~ b ) F"
  (at level 36, F at level 36, mu at level 10,
  format "'[' \int [ mu ]_( x $ a ~ b )  '/  '  F ']'").
Notation "\int [ mu ]_( x $ a ~ b ) f" :=
  (inteitv a b (fun x => f)).
*)

(*
HB.factory Record isNormedModule (K : realType) M
  of Num.NormedZmodule K M := {
}.
*)
(*
Definition pseudometric (K : realType) (M : normedZmodType K) : Type := M.

HB.instance Definition _ (K : realType) (M : normedZmodType K) :=
  Choice.on (pseudometric M).
HB.instance Definition _ (K : realType) (M : normedZmodType K) :=
  Num.NormedZmodule.on (pseudometric M).
HB.instance Definition _ (K : realType) (M : normedZmodType K) :=
  isPointed.Build M 0.
*)
(*HB.builders Context K M of isNormedModule K M.*)

(*
Section isnormedmodule.
Variables (K : realType) (M' : normedZmodType K).

Notation M := (pseudoMetric_normed M').

Local Definition ball (x : M) (r : K) : set M := ball_ Num.norm x r.

Local Definition ent : set_system (M * M) :=
  entourage_ ball.

Local Definition nbhs (x : M) : set_system M :=
  nbhs_ ent x.

Local Lemma nbhsE : nbhs = nbhs_ ent. Proof. by []. Qed.

HB.instance Definition _ := hasNbhs.Build M nbhs.

Local Lemma ball_center x (e : K) : 0 < e -> ball x e x.
Proof. by rewrite /ball/= subrr normr0. Qed.

Local Lemma ball_sym x y (e : K) : ball x e y -> ball y e x.
Proof. by rewrite /ball /= distrC. Qed.

Local Lemma ball_triangle x y z e1 e2 : ball x e1 y -> ball y e2 z ->
  ball x (e1 + e2) z.
Proof.
rewrite /ball /= => ? ?.
(*rewrite -[z](subrK y) -addrA. (le_lt_trans (ler_normD _ _))// addrC ltrD.*)
Admitted.

Local Lemma entourageE : ent = entourage_ ball.
Proof. by []. Qed.

HB.instance Definition _ := @Nbhs_isPseudoMetric.Build K M
  ent nbhsE ball ball_center ball_sym ball_triangle entourageE.

(*HB.end.*)

End isnormedmodule.
*)

HB.mixin Record isContFun (R : realType) (a b : R)
    (f : R -> R) := {
 (*{fun `[a, b] >-> [set: R]}) := { *)
  contFun : {within `[a, b], continuous f}
}.

(* TODO: rename to contFunSegmentType *)
#[short(type="contFunType")]
HB.structure Definition ContFun (R : realType) (a b : R) :=
  {f of isContFun R a b f &  @Fun R R `[a, b] [set: R] f}.

(* TODO: factory Lmodule is normed *)

HB.instance Definition _ (R : realType) (a b : R) :=
  gen_eqMixin (contFunType a b).
HB.instance Definition _ (R : realType) (a b : R) :=
  gen_choiceMixin (contFunType a b).

Section contfun_pred.
Context {R: realType}.
Variable (a b : R).
Definition contfun : {pred R -> R}
  := mem [set f | squashed (@ContFun R a b f)].
Definition contfun_key : pred_key contfun. Proof. exact. Qed.
Canonical contfun_keyed := KeyedPred contfun_key.
End contfun_pred.

Section contfun.
Context {R : realType}.
Variable (a b : R).
Notation T := (contFunType a b).

Section Sub.
Context (f : R -> R) (fP : f \in contfun a b).
Definition contfun_Sub_subproof := unsquash (set_mem fP).
#[local] HB.instance Definition _ := contfun_Sub_subproof.
Definition contfun_Sub : contFunType a b := f.
End Sub.

Lemma contfun_rect (K : T -> Type) :
  (forall f (Pf : f \in contfun a b), K (contfun_Sub Pf)) -> forall u : T, K u.
Proof.
move=> Ksub [f [[Pf]]]/=.
suff -> // : Pf = (set_mem (@mem_set _ [set f | _] f Pf)).
admit.
Admitted.

Lemma contfun_valP f (Pf : f \in contfun a b) : contfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ T contfun_rect contfun_valP.

Lemma contfuneqP (f g : contFunType a b) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of contFunType a b by <:].

Lemma cst_is_fun x : @isFun R R `[a, b] [set: R] (cst x).
Proof. by constructor. Qed.

HB.instance Definition _ x := (cst_is_fun x).

Lemma cst_continuous_subspace (x : R) : {within `[a, b], continuous (cst x)}.
Proof.
apply: continuous_subspaceT.
exact: cst_continuous.
Qed.

HB.instance Definition _ x := isContFun.Build R a b (@cst R R x)
  (@cst_continuous_subspace x).

End contfun.

Section contfun_realType.
Context {R : realType}.
Variable (a b : R).

(*
HB.instance Definition _ := @isContFun.Build R a b 
_ _ _ rT
  (@normr rT rT) (@normr_measurable rT setT).
*)

(*
HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ (@expR rT) (@measurable_expR rT).
*)

End contfun_realType.

(*
Section contfun_measurableType.
Context {d1} {T1 : measurableType d1} {d2} {T2 : measurableType d2}
  {d3} {T3 : measurableType d3}.
Variables (f : {contfun T2 >-> T3}) (g : {contfun T1 >-> T2}).

Lemma measurableT_comp_subproof : measurable_fun setT (f \o g).
Proof. exact: measurableT_comp. Qed.

HB.instance Definition _ := isMeasurableFun.Build _ _ _ _ (f \o g)
  measurableT_comp_subproof.

End contfun_measurableType.
*)

Section ring.
Context {R : realType} (a b : R).

Lemma contfun_subring_closed : subring_closed (@contfun R a b).
Proof.
split=> [|f g|f g]; rewrite !inE/=.
- apply: squash.
  exact: ContFun.class.
- move=> /unsquash cf /unsquash cg.
  apply: squash.
  pose f' : contFunType a b  := HB.pack f cf.
  pose g' : contFunType a b  := HB.pack g cg.
  rewrite [f]/(f' : _ -> _).
  rewrite [g]/(g' : _ -> _).
  move: {f g cf cg} f' g' => f g.
  have isfun_fg : @isFun R R `[a, b] [set: R] (f \- g) by constructor.
  have iscontfun_fg : @isContFun R a b (f \- g).
    constructor.
    move=> x.
    by apply: continuousB; exact: contFun.
  by split.
- move=> /unsquash cf /unsquash cg.
  apply: squash.
  pose f' : contFunType a b  := HB.pack f cf.
  pose g' : contFunType a b  := HB.pack g cg.
  rewrite [f]/(f' : _ -> _).
  rewrite [g]/(g' : _ -> _).
  move: {f g cf cg} f' g' => f g.
  have isfun_fg : @isFun R R `[a, b] [set: R] (f \- g) by constructor.
  have iscontfun_fg : @isContFun R a b (f \* g).
    constructor.
    move=> x.
    by apply: (@continuousM _ (subspace `[a, b])); exact: contFun.
  by split.
Qed.

HB.instance Definition _ := GRing.isSubringClosed.Build _
  (@contfun R a b) contfun_subring_closed.
HB.instance Definition _ := [SubChoice_isSubComRing of @contFunType R a b by <:].

Lemma contfun_scaler_closed : GRing.scaler_closed (@contfun R a b).
Proof.
move=> r f; rewrite 2!inE/=.
move/unsquash => [[cf _]].
apply: squash.
split => //.
constructor.
move=> x.
apply: continuousZ.
  exact: cst_continuous.
exact: cf.
Qed.

HB.instance Definition _ := GRing.isScaleClosed.Build _ _
  (@contfun R a b) contfun_scaler_closed.
HB.howto contFunType lmodType.

HB.instance Definition _ := [SubZmodule_isSubLmodule of @contFunType R a b by <:].
Check @contFunType R a b : lmodType _.

(*
Implicit Types (f g : {contfun aT >-> rT}).

Lemma contfun0 : (0 : {contfun aT >-> rT}) =1 cst 0 :> (_ -> _). Proof. by []. Qed.
Lemma contfun1 : (1 : {contfun aT >-> rT}) =1 cst 1 :> (_ -> _). Proof. by []. Qed.
Lemma contfunN f : - f = \- f :> (_ -> _). Proof. by []. Qed.
Lemma contfunD f g : f + g = f \+ g :> (_ -> _). Proof. by []. Qed.
Lemma contfunB f g : f - g = f \- g :> (_ -> _). Proof. by []. Qed.
Lemma contfunM f g : f * g = f \* g :> (_ -> _). Proof. by []. Qed.
Lemma contfun_sum I r (P : {pred I}) (f : I -> {contfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma contfun_prod I r (P : {pred I}) (f : I -> {contfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma contfunX f n : f ^+ n = (fun x => f x ^+ n) :> (_ -> _).
Proof. by apply/funext=> x; elim: n => [|n IHn]//; rewrite !exprS contfunM/= IHn. Qed.

HB.instance Definition _ f g := MeasurableFun.copy (f \+ g) (f + g).
HB.instance Definition _ f g := MeasurableFun.copy (\- f) (- f).
HB.instance Definition _ f g := MeasurableFun.copy (f \- g) (f - g).
HB.instance Definition _ f g := MeasurableFun.copy (f \* g) (f * g).

Definition mindic (D : set aT) of measurable D : aT -> rT := \1_D.

Lemma mindicE (D : set aT) (mD : measurable D) :
  mindic mD = (fun x => (x \in D)%:R).
Proof. by rewrite /mindic funeqE => t; rewrite indicE. Qed.

HB.instance Definition _ D mD := @isMeasurableFun.Build _ _ aT rT (mindic mD)
  (@measurable_indic _ aT rT setT D mD).

Definition indic_contfun (D : set aT) (mD : measurable D) : {contfun aT >-> rT} :=
  mindic mD.

HB.instance Definition _ k f := MeasurableFun.copy (k \o* f) (f * cst k).
Definition scale_contfun k f : {contfun aT >-> rT} := k \o* f.

Lemma max_contfun_subproof f g : @isMeasurableFun d _ aT rT (f \max g).
Proof. by split; apply: measurable_maxr. Qed.

HB.instance Definition _ f g := max_contfun_subproof f g.

Definition max_contfun f g : {contfun aT >-> _} := f \max g.

End ring.
Arguments indic_contfun {d aT rT} _.
(* TODO: move earlier?*)
#[global] Hint Extern 0  (measurable_fun _ (\1__ : _ -> _)) =>
  (exact: measurable_indic ) : core.

Section sfun_pred.
Context {d} {aT : sigmaRingType d} {rT : realType}.
Definition sfun : {pred _ -> _} := [predI @contfun _ _ aT rT & ficontfun].
Definition sfun_key : pred_key sfun. Proof. exact. Qed.
Canonical sfun_keyed := KeyedPred sfun_key.
Lemma sub_sfun_contfun : {subset sfun <= contfun}. Proof. by move=> x /andP[]. Qed.
Lemma sub_sfun_ficontfun : {subset sfun <= ficontfun}. Proof. by move=> x /andP[]. Qed.
End sfun_pred.

Section sfun.
Context {d} {aT : measurableType d} {rT : realType}.
Notation T := {sfun aT >-> rT}.
Notation sfun := (@sfun _ aT rT).
Section Sub.
Context (f : aT -> rT) (fP : f \in sfun).
Definition sfun_Sub1_subproof :=
  @isMeasurableFun.Build d _ aT rT f (set_mem (sub_sfun_contfun fP)).
#[local] HB.instance Definition _ := sfun_Sub1_subproof.
Definition sfun_Sub2_subproof :=
  @FiniteImage.Build aT rT f (set_mem (sub_sfun_ficontfun fP)).

Import HBSimple.

#[local] HB.instance Definition _ := sfun_Sub2_subproof.
Definition sfun_Sub := [sfun of f].
End Sub.

Lemma sfun_rect (K : T -> Type) :
  (forall f (Pf : f \in sfun), K (sfun_Sub Pf)) -> forall u : T, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2]]]; have Pf : f \in sfun by apply/andP; rewrite ?inE.
have -> : Pf1 = set_mem (sub_sfun_contfun Pf) by [].
have -> : Pf2 = set_mem (sub_sfun_ficontfun Pf) by [].
exact: Ksub.
Qed.

Import HBSimple.

Lemma sfun_valP f (Pf : f \in sfun) : sfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ T sfun_rect sfun_valP.

Lemma sfuneqP (f g : {sfun aT >-> rT}) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of {sfun aT >-> rT} by <:].

(* NB: already instantiated in cardinality.v *)
HB.instance Definition _ x : @FIcontfun aT rT (cst x) := FIcontfun.on (cst x).

Definition cst_sfun x : {sfun aT >-> rT} := cst x.

Lemma cst_sfunE x : @cst_sfun x =1 cst x. Proof. by []. Qed.

End sfun.

(* a better way to refactor function stuffs *)
Lemma fctD (T : pointedType) (K : ringType) (f g : T -> K) : f + g = f \+ g.
Proof. by []. Qed.
Lemma fctN (T : pointedType) (K : ringType) (f : T -> K) : - f = \- f.
Proof. by []. Qed.
Lemma fctM (T : pointedType) (K : ringType) (f g : T -> K) : f * g = f \* g.
Proof. by []. Qed.
Lemma fctZ (T : pointedType) (K : ringType) (L : lmodType K) k (f : T -> L) :
   k *: f = k \*: f.
Proof. by []. Qed.
Arguments cst _ _ _ _ /.
Definition fctWE := (fctD, fctN, fctM, fctZ).

Section ring.
Context d (aT : measurableType d) (rT : realType).

Lemma sfun_subring_closed : subring_closed (@sfun d aT rT).
Proof.
by split=> [|f g|f g]; rewrite ?inE/= ?rpred1//;
   move=> /andP[/= mf ff] /andP[/= mg fg]; rewrite !(rpredB, rpredM).
Qed.

HB.instance Definition _ := GRing.isSubringClosed.Build _ sfun
  sfun_subring_closed.
HB.instance Definition _ := [SubChoice_isSubComRing of {sfun aT >-> rT} by <:].

Implicit Types (f g : {sfun aT >-> rT}).

Import HBSimple.

Lemma sfun0 : (0 : {sfun aT >-> rT}) =1 cst 0. Proof. by []. Qed.
Lemma sfun1 : (1 : {sfun aT >-> rT}) =1 cst 1. Proof. by []. Qed.
Lemma sfunN f : - f =1 \- f. Proof. by []. Qed.
Lemma sfunD f g : f + g =1 f \+ g. Proof. by []. Qed.
Lemma sfunB f g : f - g =1 f \- g. Proof. by []. Qed.
Lemma sfunM f g : f * g =1 f \* g. Proof. by []. Qed.
Lemma sfun_sum I r (P : {pred I}) (f : I -> {sfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma sfun_prod I r (P : {pred I}) (f : I -> {sfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma sfunX f n : f ^+ n =1 (fun x => f x ^+ n).
Proof. by move=> x; elim: n => [|n IHn]//; rewrite !exprS sfunM/= IHn. Qed.

HB.instance Definition _ f g := MeasurableFun.copy (f \+ g) (f + g).
HB.instance Definition _ f g := MeasurableFun.copy (\- f) (- f).
HB.instance Definition _ f g := MeasurableFun.copy (f \- g) (f - g).
HB.instance Definition _ f g := MeasurableFun.copy (f \* g) (f * g).
*)

End ring.

Section zmodule_normed.
Context {R : realType} (a b : R).

Definition infty_norm (f : {fun `[a, b] >-> [set: R]}) :=
  sup ((Num.norm \o f) @` `[a, b]).

Local Notation V := (contFunType a b).

Local Notation norm := infty_norm.

(* TODO: wait for quotient *)
Lemma contfuneqP' (f g : contFunType a b) : f = g <-> {in `[a, b], f =1 g}.
Proof.
split=> [->//|].
move: f g => [f [[cf]] [funf]] [g [[cg]] [fung]].
move=> /= fg.
Admitted.

Local Lemma ler_normD (x y : V) : norm (x + y) <= norm x + norm y :> R.
Proof.
Admitted.

Local Lemma normr0_eq0 (x : V) : norm x = 0 -> x = 0.
Proof.
Admitted.

Local Lemma normrMn (x : V) n : norm (x *+ n) = norm x *+ n.
Admitted.

Local Lemma normrN (x : V) : norm (- x) = norm x.
Admitted.
(* TODO: dev the theory of sup following the theory of ess_sup *)

Fail Check V : normedZmodType R.

HB.instance Definition _ := @Num.Zmodule_isNormed.Build R V
  norm ler_normD normr0_eq0 normrMn normrN.

Check V : normedZmodType R.

Check (pseudoMetric_normed V) : pseudoMetricType R.
Check (pseudoMetric_normed V) : normedZmodType R.
Fail Check (pseudoMetric_normed V) : normedModType R.

End zmodule_normed.

HB.about Lmodule_isNormed.

(*
HB.factory Record Lmodule_isNormed (R : realType) M
    of GRing.Lmodule R M := {
 norm : M -> R;
 ler_normD : forall x y, norm (x + y) <= norm x + norm y ;
(* normrMn : forall x n, norm (x *+ n) = norm x *+ n ;*)
 normrN : forall x, norm (- x) = norm x ;
 normrZ : forall (l : R) (x : M), norm (l *: x) = `|l| * norm x ;
 normr0_eq0 : forall x : M, norm x = 0 -> x = 0
}.

HB.builders Context R M of Lmodule_isNormed R M.

HB.about Num.Zmodule_isNormed.Build.

Lemma normrMn x n : norm (x *+ n) = norm x *+ n.
Proof.
move: x.
rewrite /=.
Admitted. (* from normrZ *)

HB.instance Definition _ := Num.Zmodule_isNormed.Build
  R M ler_normD normr0_eq0 normrMn normrN.

Check M : normedZmodType R.

Check (@pseudometric R M).

HB.saturate pseudometric.

Check (pseudometric M : pseudoMetricType R).

HB.instance Definition _ := PseudoMetric.copy M (pseudometric M).
HB.instance Definition _ := isPointed.Build M 0.

Lemma whatever : NormedZmod_PseudoMetric_eq R M.
Proof.
by constructor.
Qed.

HB.instance Definition _ := whatever.

Lemma coucou : PseudoMetricNormedZmod_Lmodule_isNormedModule R M.
Proof.
constructor.
exact: normrZ.
Qed.

HB.instance Definition _ := coucou.
HB.instance Definition _ := isPointed.Build M 0.

Check M : normedModType R.

HB.end.
*)

Section picard_method.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Variables (f : R -> R -> R) (y_ : R -> R) (d : R).
Hypothesis (d0 : 0 < d).
Local Notation contFunType x := (contFunType (- x) x).

Variables ( k : R).
Hypothesis (lcf_x : {in `[- d, d], forall y, k.-lipschitz (f^~ y)}).
Hypothesis (cf_y : {in `[- d, d], forall x, {within `[-d, d], continuous f x}}).

Hypothesis (y_init_t : y_ 0 = 0).

Definition picard_method'' (g : (contFunType d)) := (fun t =>
   (\int[mu]_(x in `[- d, t]) f x (g x))%R
       - (\int[mu]_(x in `[- d, d]) f x (g x))%R).

Local Lemma set_fun_picard g :
   {homo picard_method'' g : x / `[- d, d] x >-> [set: R] x}.
Proof. by []. Qed.

HB.instance Definition _ g :=
    @isFun.Build _ _ `[- d, d] setT (picard_method'' g) (set_fun_picard g).

Local Lemma picard_method_is_contfun (g : (contFunType d)) :
  @isContFun R (- d) d (picard_method'' g).
Proof.
constructor.
(* *)
Admitted.

HB.instance Definition _ (g : (contFunType d)) :=
(@picard_method_is_contfun g).

Local Lemma continuous_picard_method (g : (contFunType d)) :
  {within `[- d, d], continuous picard_method'' g}.
Proof.
exact: contFun.
Qed.

Local Definition picard_method' (g : (contFunType d)) : (contFunType d)
    := picard_method'' g.

Local Lemma set_fun_picard_method :
   {homo picard_method' : g /
       [set: (contFunType d)] g >-> [set: (contFunType d)] g}.
Proof. by []. Qed.

HB.instance Definition _ :=
    @isFun.Build _ _ _ _ picard_method' set_fun_picard_method.

Definition picard_method :
    {fun [set: (contFunType d)] >-> [set: (contFunType d)]}
  := picard_method'.

End picard_method.

Section picard_sketch.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Local Notation contFunType x := (contFunType (- x) x).

HB.instance Definition _ {r : R} := PseudoMetric.copy (contFunType r)
   (pseudoMetric_normed (contFunType r)).
HB.instance Definition _ {r} := isPointed.Build (contFunType r) (@cst R R 0).

Variables (f : R -> R -> R) (y_ : R -> R) (d : R).
Hypothesis (d0 : 0 < d).

Variables ( k : R).
Hypothesis (lcf_x : {in `[- d, d], forall y, k.-lipschitz (f^~ y)}).
Hypothesis (cf_y : {in `[- d, d], forall x, {within `[-d, d], continuous f x}}).

Hypothesis (y_init_t : y_ 0 = 0).

Lemma is_normZmod_contFunTypee : NormedZmod_PseudoMetric_eq R (contFunType d).
Proof.
by constructor.
Qed.

HB.instance Definition _ := is_normZmod_contFunTypee.

Lemma is_pmnormedZmod_contFunTypee :
  PseudoMetricNormedZmod_Lmodule_isNormedModule R (contFunType d).
Proof.
constructor.
Admitted.

HB.instance Definition _ := Num.Zmodule_isNormed.Build
  R (contFunType d) (@ler_normD R (- d) d) (@normr0_eq0 R (- d) d)
  (@normrMn R (- d) d) (@normrN R (- d) d).

HB.instance Definition _ := is_pmnormedZmod_contFunTypee.

Notation picard_method := (picard_method d0 lcf_x cf_y y_init_t).

Lemma ctr_picard : is_contraction picard_method.
Proof.
red.
rewrite /contraction.
Admitted.

Let phi0 := (@cst R R 0%R). (* 0 is init_y *)

Check phi0 : contFunType d.

Let phioo := (limn (fun n => iter n picard_method phi0)) : R -> R.

Lemma picard_theorem :
 phioo 0 = 0 /\
  ({in `]- d, d[, forall x, phioo^`() x = f x (phioo x)}).
Proof.
split.
rewrite /phioo.

(*
set picard_method : (contFunType d) -> (contFunType d) := (fun (g : (contFunType d)) => (fun t =>
   init_y
     + (\int[mu]_(x in `[init_t - e, t]) f x (g x))%R
       - (\int[mu]_(x in `[init_t - e, init_t]) f x (g x))%R)).
   (* add properties which should be preserved *))
).
have : (forall g , {h | rel g h}).
  admit.
move/dependent_choice/(_ phi0); rewrite /rel => -[phi_ [phi0eq /all_and2[cphi iter_phi]]].
(* phioo should be (limn (fun n => iter n picard_method phi0). *)
set phioo := (fun x => lim ((phi_ n x) @[n --> \oo])).
have cphioo : {in `]init_t - e, init_t + e[, continuous phioo}.
  move=> x xte.
  apply/cvgrPdist_le => eps eps0.
  near \oo => N. (* forall n > N satisfies
       (forall x, `|phi_ N x - phioo x| < eps / 3 *)
  near (@GRing.zero R)^'+ => dlt. (* forall t in ball x t satisfies
       ( `|phi_ N x - phi_ N t| < eps / 3 *)
  exists dlt.
    admit.
  move=> t/= tadlt.
  rewrite (_ : eps = eps / 3 + (eps / 3 + eps / 3)); last first.
    admit.
  rewrite -[phioo x](subrK (phi_ N x)).
  rewrite -[_ + _]addrA.
  rewrite -{2}[phi_ N x](subrK (phi_ N t)).
  rewrite -[X in _ + X]addrA.
  apply: (le_trans (ler_normD (phioo x - phi_ N x)%R _)); apply: lerD.
    admit.
  apply: (le_trans (ler_normD (phi_ N x - phi_ N t)%R _)); apply: lerD.
    admit.
  admit.
exists phioo.
split.
  apply/cvg_lim => //.
  apply: cvg_near_cst.
  apply/nearW => n.
  elim: n.
    by rewrite phi0eq.
  by move=> n IH; rewrite iter_phi -addrA subrr addr0.
move=> x xte.
(* exact: contraction_cvg_fixed *)
admit.
*)
Admitted.

End picard_sketch.


(* dy = f(t, y(t)), y(t0) = y0 *)
Record IVP (R : realType) := {
  time_domain : interval R ;
  open_time_domain : open [set` time_domain] ;
  value_domain : interval R ;
  rhs : R -> R -> R ;
  initial_time : R (* t0 *) ;
  initial_time_domain : initial_time \in time_domain ;
  initial_value : R (* y0 *) ;
  initial_value_domain : initial_value \in value_domain ;
}.

Section solution_of_an_IVP.
Context {R : realType}.
Variable pbm : @IVP R.

Let t0 := initial_time pbm.
Let y0 := initial_value pbm.
Let rhs := rhs pbm.

Definition solution (i : interval R) (y : R -> R) :=
  [/\ t0 \in i,
      open [set` i],
      y @` [set` time_domain pbm] `<=` [set` value_domain pbm],
      {in i, forall t, y^`() t = rhs t (y t)} &
      y t0 = y0 ].

Let i := time_domain pbm.
Let j := value_domain pbm.
Hypothesis rhs_cont : forall y, y \in j -> {in i, continuous (rhs ^~ y)}.
Hypothesis rhs_lip : forall x, x \in i -> [lipschitz rhs x y | y in [set: R]].

Let mu := @lebesgue_measure R.

Definition inte a b f :=
  if a < b then \int[mu]_(x in `[a, b]) f x else - \int[mu]_(x in `[b, a]) f x.

Reserved Notation "\int [ mu ]_( x $ a ~ b ) F"
  (at level 36, F at level 36, mu at level 10,
  format "'[' \int [ mu ]_( x $ a ~ b )  '/  '  F ']'").

Notation "\int [ mu ]_( x $ a ~ b ) f" :=
  (inte a b (fun x => f)).

Lemma picard : exists (i : interval R) (y : R -> R), solution i y.
Proof.
pose f (y : R -> R) (t : R) := y0 + \int[mu]_(x $ t0 ~ t) rhs x (y x).
(* have : is_contraction f. *)
Abort.

End solution_of_an_IVP.
