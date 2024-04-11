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

Reserved Notation "{ 'inner_measure' fUV }"
  (at level 0, format "{ 'inner_measure'  fUV }").
Reserved Notation "[ 'inner_measure' 'of' f 'as' g ]"
  (at level 0, format "[ 'inner_measure'  'of'  f  'as'  g ]").
Reserved Notation "[ 'inner_measure' 'of' f ]".

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

(* TODO : Is this needed? *)
Definition sigma_superadditive {T} {R : numFieldType}
  (mu : set T -> \bar R) := forall (F : (set T) ^nat), trivIset setT F ->
    (\sum_(i <oo) mu (F i) <= mu (\bigcup_n (F n)))%E.

HB.mixin Record isInnerMeasure
    (R : numFieldType) (T : Type) (mu : set T -> \bar R) := {
  inner_measure0 : mu set0 = 0 ;
  inner_measure_ge0 : forall x, (0 <= mu x)%E ;
  inner_measure_sigma_superadditive : sigma_superadditive mu }.

#[short(type= inner_measure)]
HB.structure Definition InnerMeasure (R : numFieldType) (T : Type) :=
  {mu & isInnerMeasure R T mu}.

Notation "{ 'inner_measure' 'set' T '->' '\bar' R }" := (inner_measure R T)
  (at level 36, T, R at next level,
    format "{ 'inner_measure'  'set'  T  '->'  '\bar'  R }") : ring_scope.

#[global] Hint Extern 0 (_ set0 = 0%R) => solve [apply: inner_measure0] : core.
#[global] Hint Extern 0 (sigma_superadditive _) =>
  solve [apply: inner_measure_sigma_superadditive] : core.

Arguments inner_measure0 {R T} _.
Arguments inner_measure_ge0 {R T} _.
Arguments inner_measure_sigma_superadditive {R T} _.

Lemma le_inner_measure {T : Type} {R : realType}
  (mu : {inner_measure set T -> \bar R})
  : {homo mu : A B / A `<=` B >-> (A <= B)%E}.
Proof.
move=> A B AB.
apply: (@le_trans _ _ (mu A + mu (B `\` A))).
- apply: lee_addl.
  exact: inner_measure_ge0.
- pose F i := match i with 0%N => A | 1%N => B `\` A | _ => set0 end.
  have -> : (mu A + mu (B `\` A) = \sum_(i <oo) mu (F i))%E.
    apply: esym.
    apply: cvg_lim => //.
    apply: cvg_near_cst.
    exists 2%N => // n /= n0.
    rewrite -(subnK n0) addn2.
    rewrite !big_nat_recl /=; last 2 first.
        by rewrite leq_subRL // addn0 ltnW // leq0Sn.
      by rewrite ltnW // leq0Sn.
    rewrite inner_measure0.
    rewrite big_const_nat.
    rewrite iter_addr_0.
    rewrite mul0rn.
    by rewrite addr0.
  have -> : B = \bigcup_i F i.
    rewrite (bigcup_splitn 2%N).
    rewrite !big_ord_recl /=.
    rewrite big_const_ord /= setU0.
    rewrite bigcup_const ?setU0; last by exists 0%N.
    by apply: esym; apply: setDUK.
  apply: inner_measure_sigma_superadditive.
  have -> : F = bigcup2 A (B `\` A).
    apply: funext.
    rewrite /F.
    by case; last case.
  rewrite -trivIset_bigcup2.
  exact: setDIK.
Qed.

Lemma inner_measure_sigma_superadditive_tail (T : Type) (R : realType)
    (mu : {inner_measure set T -> \bar R}) N (F : (set T) ^nat) :
  trivIset (~` `I_N) F ->
  (\sum_(N <= i <oo) mu (F i) <= mu (\bigcup_(n in ~` `I_N) (F n)))%E.
Proof.
move=> triF.
rewrite bigcup_mkcond.
have triF' : trivIset [set: nat] (fun n => if n \in ~` `I_N then F n else set0).
  by apply/(trivIset_mkcond (~` `I_N)).
have := inner_measure_sigma_superadditive mu
  (fun n => if n \in ~` `I_N then F n else set0).
move/(_ triF').
apply: le_trans.
rewrite [in leLHS]eseries_cond [in leLHS]eseries_mkcondr; apply: lee_nneseries.
- by move=> k _; rewrite fun_if; case: ifPn => Nk //; rewrite inner_measure_ge0.
- move=> k _.
  case: ifPn => Nk; last by rewrite inner_measure_ge0.
  by case: ifPn; rewrite mem_not_I; move/negP.
Qed.

Section inner_measureU.
Context d (T : semiRingOfSetsType d) (R : realType).
Variable mu : {inner_measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma inner_measure_superadditive (F : nat -> set T) n :
trivIset [set k : nat | (k < n)%N] F ->
  \sum_(i < n) mu (F i) <= mu (\big[setU/set0]_(i < n) F i).
Proof.
move=> trivF.
pose F' := fun k => if (k < n)%N then F k else set0.
have trivF' : trivIset [set: nat] F'.
  rewrite /F'.
  suff -> : (fun k : nat => if (k < n)%N then F k else set0) = (fun k=> if k \in `I_n then F k else set0 ) by rewrite -(trivIset_mkcond).
  apply: funext => k.
  case: ifP => Hkn; first by rewrite ifT // inE.
  rewrite ifF //.
  apply: memNset.
  by rewrite /= Hkn.
rewrite -(big_mkord xpredT F) big_nat (eq_bigr F')//; last first.
  by move=> k /= kn; rewrite /F' kn.
rewrite -big_nat big_mkord.
have := inner_measure_sigma_superadditive mu F'.
rewrite (bigcup_splitn n) (_ : bigcup _ _ = set0) ?setU0; last first.
  by rewrite bigcup0 // => k _; rewrite /F' /= ltnNge leq_addr.
move/(_ trivF').
apply le_trans.
rewrite (nneseries_split n); last by move=> ?; exact: inner_measure_ge0.
rewrite [X in _ + X](_ : _ = 0) ?adde0//; last first.
  rewrite eseries_cond/= eseries_mkcond eseries0//.
  by move=> k _; case: ifPn => //; rewrite /F' leqNgt => /negbTE ->.
by apply: lee_sum => i _; rewrite /F' ltn_ord.
Qed.

Lemma inner_measureU2 A B : A `&` B = set0 -> mu A + mu B <= mu (A `|` B).
Proof.
move=> ab0.
have trivab : trivIset `I_2 (bigcup2 A B).
  apply: (@sub_trivIset _ _ _ setT) => //.
  by rewrite -trivIset_bigcup2.
have := inner_measure_superadditive trivab.
by rewrite !big_ord_recl/= !big_ord0 setU0 adde0.
Qed.

End inner_measureU.

Lemma ge_inner_measureIC (R : realFieldType) T
  (mu : {inner_measure set T -> \bar R}) (A X : set T) :
  (mu (X `&` A) + mu (X `&` ~` A) <= mu X)%E.
Proof.
pose B : (set T) ^nat := bigcup2 (X `&` A) (X `&` ~` A).
have trivB : trivIset setT B.
  rewrite -trivIset_bigcup2.
  by rewrite setIACA setIid setIA setICK.
have cvg_mu : (fun n => \sum_(i < n) mu (B i)) @ \oo --> mu (B 0%N) + mu (B 1%N).
  rewrite -2!cvg_shiftS /=.
  rewrite [X in X @ \oo --> _](_ : _ = (fun=> mu (B 0%N) + mu (B 1%N))); last first.
    rewrite funeqE => i; rewrite 2!big_ord_recl /= big1 ?adde0 // => j _.
    by rewrite /B /bigcup2 /=.
  exact: cvg_cst.
have := inner_measure_sigma_superadditive mu B trivB.
suff : \bigcup_n B n = X.
  move=> ->; apply: le_trans; under eq_fun do rewrite big_mkord.
  by rewrite (cvg_lim _ cvg_mu).
transitivity (\big[setU/set0]_(i < 2) B i).
  by rewrite (bigcup_splitn 2) // -bigcup_mkord setUidl// => t -[].
by rewrite 2!big_ord_recl big_ord0 setU0 /= -setIUr setUCr setIT.
Unshelve. all: by end_near. Qed.

(* Section inner_measure_construction. *)
(* Local Open Scope ereal_scope. *)
(* Context (R : realType). *)
(* Variable mu : set R -> \bar R. *)
(* Hypothesis (measure0 : mu set0 = 0) (measure_ge0 : forall X, mu X >= 0). *)
(* Hint Resolve measure_ge0 measure0 : core. *)

(* Lemma ex_outer_approx_fin (X : set R) : (mu^* )%mu X < +oo -> *)
(* forall eps : R, (0 < eps)%R -> exists J : set R, *)
(*   [/\ open J, X `<=` J & mu J - (mu^* )%mu X < eps%:E]. *)
(* Proof. *)
(* Admitted. *)

(* Lemma ex_outer_approx (X : set R) : *)
(* exists J_ : (set R)^nat, forall i, open (J_ i) /\ J_ i `<=` X `&` `[ -%R i%:R, i%:R]%classic *)
(*   /\ (mu^* )%mu (X `&` `[-%R i%:R, i%:R]%classic) - (mu^* )%mu (J_ i) < (2^-1 ^+ i)%:E. *)

(* Let outer_open (X : set R) (finX : (mu^* )%mu X < +oo) := *)
(*    fun e : R => proj1_sig (cid (ex_outer_approx finX e)). *)

(* Definition mu_inext (X : set T) : \bar R := if pselect (mu^* X < +oo) then *)
(*  mu^* (outer_open X) - ereal_inf [set \sum_(k <oo) mu (A k) | A in measurable_cover ((outer_open X) `&` ~` X)]. else +oo *)
(* Local Notation "mu_*" := mu_inext. *)

(* Lemma le_mu_inext : {homo mu^* : A B / A `<=` B >-> A <= B}. *)
(* Proof. *)
(* move=> A B AB; apply/le_ereal_inf => x [B' [mB' BB']]. *)
(* by move=> <-{x}; exists B' => //; split => //; apply: subset_trans AB BB'. *)
(* Qed. *)

(* Lemma mu_inext_ge0 A : 0 <= mu_* A. *)
(* Proof. *)
(* apply: lb_ereal_inf => x [B [mB AB] <-{x}]; rewrite lime_ge //=. *)
(*   exact: is_cvg_nneseries. *)
(* by near=> n; rewrite sume_ge0. *)
(* Unshelve. all: by end_near. Qed. *)

(* Lemma mu_inext0 : mu_* set0 = 0. *)
(* Proof. *)
(* apply/eqP; rewrite eq_le; apply/andP; split; last exact/mu_ext_ge0. *)
(* rewrite /mu_ext; apply: ereal_inf_lb; exists (fun=> set0); first by split. *)
(* by apply: lim_near_cst => //; near=> n => /=; rewrite big1. *)
(* Unshelve. all: by end_near. Qed. *)

(* Lemma mu_inext_sigma_superadditive : sigma_superadditive mu^*. *)
(* Proof. *)
(* move=> A; have [[i ioo]|] := pselect (exists i, mu^* (A i) = +oo). *)
(*   rewrite (eseries_pinfty _ _ ioo) ?leey// => n _. *)
(*   by rewrite -ltNye (lt_le_trans _ (mu_ext_ge0 _)). *)
(* rewrite -forallNE => Aoo. *)
(* suff add2e (e : {posnum R}) : *)
(*     mu^* (\bigcup_n A n) <= \sum_(i <oo) mu^* (A i) + e%:num%:E. *)
(*   by apply/lee_addgt0Pr => _/posnumP[]. *)
(* rewrite (le_trans _ (epsilon_trick _ _ _))//; last first. *)
(*   by move=> n; exact: mu_ext_ge0. *)
(* pose P n (B : (set T)^nat) := measurable_cover (A n) B /\ *)
(*   \sum_(k <oo) mu (B k) <= mu^* (A n) + (e%:num / (2 ^ n.+1)%:R)%:E. *)
(* have [G PG] : {G : ((set T)^nat)^nat & forall n, P n (G n)}. *)
(*   apply: (@choice _ _ P) => n; rewrite /P /mu_ext. *)
(*   set S := (X in ereal_inf X); move infS : (ereal_inf S) => iS. *)
(*   case: iS infS => [r Sr|Soo|Soo]. *)
(*   - have en1 : (0 < e%:num / (2 ^ n.+1)%:R)%R by []. *)
(*     have /(lb_ereal_inf_adherent en1) : ereal_inf S \is a fin_num by rewrite Sr. *)
(*     move=> [x [B [mB AnB muBx] xS]]. *)
(*     by exists B; split => //; rewrite muBx -Sr; exact/ltW. *)
(*   - by have := Aoo n; rewrite /mu^* Soo. *)
(*   - suff : lbound S 0 by move/lb_ereal_inf; rewrite Soo. *)
(*     by move=> /= _ [B [mB AnB] <-]; exact: nneseries_ge0. *)
(* have muG_ge0 x : 0 <= (mu \o uncurry G) x by exact: measure_ge0. *)
(* apply: (@le_trans _ _ (\esum_(i in setT) (mu \o uncurry G) i)). *)
(*   rewrite /mu_ext; apply: ereal_inf_lb => /=. *)
(*   have /card_esym/ppcard_eqP[f] := card_nat2. *)
(*   exists (uncurry G \o f). *)
(*     split => [i|]; first exact/measurable_uncurry/(PG (f i).1).1.1. *)
(*     apply: (@subset_trans _  (\bigcup_n \bigcup_k G n k)) => [t [i _]|]. *)
(*       by move=> /(cover_subset (PG i).1) -[j _ ?]; exists i => //; exists j. *)
(*     move=> t [i _ [j _ Bijt]]; exists (f^-1%FUN (i, j)) => //=. *)
(*     by rewrite invK ?inE. *)
(*   rewrite -(esum_pred_image (mu \o uncurry G) _ xpredT) ?[fun=> _]set_true//. *)
(*   by rewrite image_eq. *)
(* rewrite (_ : esum _ _ = \sum_(i <oo) \sum_(j <oo ) mu (G i j)); last first. *)
(*   pose J : nat -> set (nat * nat) := fun i => [set (i, j) | j in setT]. *)
(*   rewrite (_ : setT = \bigcup_k J k); last first. *)
(*     by rewrite predeqE => -[a b]; split => // _; exists a => //; exists b. *)
(*   rewrite esum_bigcupT /=; last 2 first. *)
(*     - apply/trivIsetP => i j _ _ ij. *)
(*       rewrite predeqE => -[n m] /=; split => //= -[] [_] _ [<-{n} _]. *)
(*       by move=> [m' _] [] /esym/eqP; rewrite (negbTE ij). *)
(*     - by move=> /= [n m]; apply: measure_ge0; exact: (cover_measurable (PG n).1). *)
(*   rewrite -(image_id [set: nat]) -fun_true esum_pred_image//; last first. *)
(*     by move=> n _; exact: esum_ge0. *)
(*   apply: eq_eseriesr => /= j _. *)
(*   rewrite -(esum_pred_image (mu \o uncurry G) (pair j) predT)//=; last first. *)
(*     by move=> ? ? _ _; exact: (@can_inj _ _ _ snd). *)
(*   by congr esum; rewrite predeqE => -[a b]; split; move=> [i _ <-]; exists i. *)
(* apply: lee_lim. *)
(* - apply: is_cvg_nneseries => n _. *)
(*   by apply: nneseries_ge0 => m _; exact: (muG_ge0 (n, m)). *)
(* - by apply: is_cvg_nneseries => n _; apply: adde_ge0 => //; exact: mu_ext_ge0. *)
(* - by near=> n; apply: lee_sum => i _; exact: (PG i).2. *)
(* Unshelve. all: by end_near. Qed. *)

(* End inner_measure_construction. *)

(* TODO: move to sequences.v *)
Lemma nneseries_addn (R : realType) (k : nat) (f : nat -> \bar R) :
  (forall i, 0 <= f i)%E ->
  (\sum_(k <= i <oo) f i = \sum_(0 <= i <oo) (f (i + k)%N))%E.
Proof.
move=> f0; have /cvg_ex[/= l fl] : cvg (\sum_(k <= i < n) f i @[n --> \oo]).
  by apply: ereal_nondecreasing_is_cvgn => m n mn; exact: lee_sum_nneg_natr.
rewrite (cvg_lim _ fl)//; apply/esym/cvg_lim => //=.
move: fl; rewrite -(cvg_shiftn k) /=.
by under eq_fun do rewrite -{1}(add0n k)// big_addn addnK.
Qed.

Lemma bigcap_series_addn (R : realType) (k : nat) (B : nat -> set R) :
  (\bigcap_(j in [set j | (k <= j)%N]) B j = \bigcap_i (B (i + k)%N)).
Proof.
rewrite eqEsubset; split.
- rewrite /bigcap => x /= H n _.
  apply:H.
  exact: leq_addl.
- rewrite /bigcap => x /= H n ki.
  rewrite -(subnK ki).
  by apply: H.
Qed.

Section move_to_realfun.
Context {R : realType}.

Lemma total_variation_nondecreasing a b (f : R -> R) :
  bounded_variation a b f ->
  {in `[a, b] &, {homo fine \o (total_variation a ^~ f) : x y / x <= y}}.
Proof.
move=> BVf x y; rewrite !in_itv/= => /andP[ax xb] /andP[ay yb] xy.
rewrite fine_le //.
- exact/(bounded_variationP _ ax)/(bounded_variationl ax xb).
- exact/(bounded_variationP _ ay)/(bounded_variationl ay yb).
- by rewrite (total_variationD f ax xy)// lee_addl// total_variation_ge0.
Qed.

Lemma total_variation_bounded a b (f : R -> R) : a <= b ->
  bounded_variation a b f ->
  bounded_variation a b (fine \o (total_variation a ^~ f)).
Proof.
move=> ab BVf; apply/bounded_variationP => //.
rewrite ge0_fin_numE; last exact: total_variation_ge0.
rewrite nondecreasing_total_variation/= ?ltry//.
exact: total_variation_nondecreasing.
Qed.

End move_to_realfun.

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
End for_abs_cont.

Section absolute_continuity.
Context {R : realType}.

Definition abs_cont (a b : R) (f : R -> R) := forall e : {posnum R},
  exists d : {posnum R}, forall n (B : 'I_n -> R * R),
    [/\ (forall i, (B i).1 < (B i).2 /\ `](B i).1, (B i).2[ `<=` `[a, b]),
        trivIset setT (fun i => `](B i).1, (B i).2[%classic) &
        \sum_(k < n) ((B k).2 - (B k).1) < d%:num] ->
    \sum_(k < n) (f (B k).2 - f ((B k).1)) < e%:num.

Lemma total_variation_AC a b (f : R -> R) : a < b ->
  bounded_variation a b f ->
  abs_cont a b (fine \o (total_variation a ^~ f)) -> abs_cont a b f.
Proof.
move=> ab BVf + e => /(_ e)[d ACf].
exists d => n B HB; have {ACf} := ACf n B HB.
move: HB => [/all_and2[B12 Bab]] tB sumBd sumfBe.
rewrite (le_lt_trans _ sumfBe)//; apply: ler_sum => /= i _.
have aBi1 : a <= (B i).1 by exact: incl_itv_lb.
have Bi2b : (B i).2 <= b by exact: incl_itv_ub.
rewrite (le_trans (ler_norm (f (B i).2 - f (B i).1)))//=.
rewrite (total_variationD f aBi1 (ltW (B12 _))) fineD; last 2 first.
  apply/(bounded_variationP f aBi1)/(@bounded_variationl _ _ _ b) => //.
  by rewrite (le_trans _ Bi2b)// ltW.
  apply/(bounded_variationP f (ltW (B12 _))).
  apply/(bounded_variationl (ltW (B12 _)) Bi2b).
  by apply: (bounded_variationr aBi1) => //; rewrite (le_trans _ Bi2b)// ltW.
rewrite addrAC subrr add0r -subr_ge0 -lee_fin EFinB fineK; last first.
  apply/(bounded_variationP f (ltW (B12 _))).
  apply/(bounded_variationl (ltW (B12 _)) Bi2b).
  by apply/(bounded_variationr aBi1 _ BVf); rewrite (le_trans _ Bi2b)// ltW.
by rewrite lee_subr_addr// add0e total_variation_ge// ltW.
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

Section lebesgue_measure_complete.
Context {R : realType}.

(*
  ref:https://heil.math.gatech.edu/6337/spring11/section1.1.pdf
  Lemma 1.17
*)

Lemma outer_regularity_outer0 (E : set R) (e : R) : (e > 0)%R ->
  exists U : set R, [/\ open U, E `<=` U &
   (lebesgue_measure E <= lebesgue_measure U <= lebesgue_measure E + e%:E)%E].
Proof.
move=> e0.
have [->|] := eqVneq (lebesgue_measure E) +oo%E.
  exists setT; split => //; first exact: openT.
  by rewrite lebesgue_measureT lexx.
rewrite -ltey -ge0_fin_numE; last exact: outer_measure_ge0.
move=> mEfin.
move: (mEfin) => /lb_ereal_inf_adherent.
set infE := ereal_inf _.
have infEE : infE = lebesgue_measure E by [].
have e20 : 0 < e / 2 by rewrite divr_gt0.
move=> /(_ _ e20).
move=> [x [/= Q EQ <- muEoo]].
have [/= T QT TQ] : exists2 T : nat -> set _,
  (forall k, Q k `<=` interior (T k)) &
    (forall k, lebesgue_measure (T k) <= lebesgue_measure (Q k) + (e / (2 ^+ k.+2))%:E)%E.
  rewrite /=.
  have mQfin k: lebesgue_measure (Q k) \is a fin_num.
    rewrite ge0_fin_numE; last exact: measure_ge0.
    apply: (@le_lt_trans _ _ (\big[+%R/0%R]_(0 <= k <oo) wlength idfun (Q k))).
    rewrite {1}/lebesgue_measure/=/lebesgue_stieltjes_measure/=/measure_extension/=.
    rewrite measurable_mu_extE /=; last admit.
      admit.
    apply: (lt_trans muEoo).
    admit.
  have : forall k, exists T : set R,
  [/\ open T, (Q k) `<=` T
    & ([the measure
              [the measurableType (R.-ocitv.-measurable).-sigma of 
              salgebraType R.-ocitv.-measurable] R of lebesgue_measure]
         (T `\` (Q k)) < (e / 2 ^+ k.+2)%:E)%E].
    admit.
  move/choice.
  move=> [T /= TH].
  exists T.
    admit.
  admit.
pose U := \bigcup_k interior (T k).
have EU : E `<=` U.
  case: EQ => _.
  move=> /subset_trans; apply.
  apply: subset_bigcup => k _.
  exact: QT.
exists U.
  split => //.
  apply: bigcup_open.
  move=> i _.
  exact: open_interior. (* NB: should be interior_open *)
apply/andP; split.
  exact: le_outer_measure.
rewrite (splitr e) EFinD addeA.
apply: (@le_trans _ _ (\big[+%R/0%R]_(0 <= k <oo) lebesgue_measure (Q k) + (e / 2)%:E)%E); last first.
  rewrite lee_add2r// ltW//.
  apply: le_lt_trans muEoo.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  apply: eq_eseriesr => k _.
  rewrite /= /lebesgue_measure/=/lebesgue_stieltjes_measure/=.
  rewrite /measure_extension.
  rewrite measurable_mu_extE//.
  by case: EQ.
apply: (@le_trans _ _ (\big[+%R/0%R]_(0 <= k <oo) lebesgue_measure (T k))); last first.
  apply: le_trans; last first.
    apply: epsilon_trick.
    move=> k.
    done.
    by rewrite ltW.
  apply: lee_nneseries => // k _.
  rewrite -mulrA.
  rewrite (_ : _ / _ = 1 / (2 ^+ k.+2))%R; last first.
    rewrite -invfM//.
    rewrite natrX.
    rewrite -exprS.
    by rewrite mul1r.
  rewrite mul1r.
  by have := TQ k.
rewrite /U.
apply: (@le_trans _ _ (lebesgue_measure (\bigcup_k (T k)))).
  apply: le_outer_measure.
  apply: subset_bigcup => k _.
  by apply: interior_subset.
  by have := outer_measure_sigma_subadditive lebesgue_measure T.
Admitted.

Lemma outer_regularity_outer (E : set R) :
  lebesgue_measure E = ereal_inf [set Z | exists U, [/\ Z = lebesgue_measure U, open U & E `<=` U]].
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: lb_ereal_inf => /= r /= [A [-> oA EA]] {r}.
  apply: le_ereal_inf => _ /= [] S_ AS_ <-; exists S_ => //.
  move: AS_ => [mS_ AS_].
  by split; [exact: mS_|exact: (subset_trans EA)].
- apply/lee_addgt0Pr => /= e e0.
  have [U [oU EU /andP[UE UEe]]] := outer_regularity_outer0 E e0.
  apply: ereal_inf_le => /=.
  exists (lebesgue_measure U) => //.
  by exists U.
Qed.

(*
  ref:https://heil.math.gatech.edu/6337/spring11/section1.2.pdf
  Definition 1.19. the converse of lebesgue_regularity_outer in lebesgue_measure.
*)
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

Lemma regularity_outer_lebesgue (E : set R) :
 ((lebesgue_measure) E < +oo)%E ->
 (forall eps : R, 0 < eps -> exists U, [/\ open U,
   E `<=` U &
   ((lebesgue_measure) (U `\` E) < eps%:E)%E]) -> measurable E.
Proof.
move=> /= Eley H.
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
have U0 := fun i => (H (delta_0 i) (delta_0_ge0 i)).
pose U0_ i := proj1_sig (cid (U0 i)).
have oU0 i : open (U0_ i).
  move: (projT2 (cid (U0 i))).
  by move=> [] + _ _.
have EU0 i : E `<=` U0_ i.
  move: (projT2 (cid (U0 i))).
  by move=> [] _ + _.
have mU0E i : ((lebesgue_measure) ((U0_ i) `\` E) < (delta_0 i)%:E)%E.
  move: (projT2 (cid (U0 i))).
  by move=> [] _ _ +.
pose U_ i := \bigcap_(j < i.+1) U0_ j.
have mU i : measurable (U_ i).
  apply: bigcap_measurable => n _.
  by apply: open_measurable.
have EU i : forall i, E `<=` U_ i.
  by move=> n; rewrite /U_; apply: sub_bigcap.
pose Uoo := \bigcap_i (U_ i).
have mUoo : measurable Uoo.
  apply: Gdelta_measurable.
  exists U_ => //.
  move=> n.
  rewrite /U_.
  by apply: bigcap_open.
have cvgUoo : lebesgue_measure (U_ n) @[n --> \oo] --> lebesgue_measure Uoo.
  apply: nonincreasing_cvg_mu => //=.
    rewrite /U_ bigcap_mkord.
    rewrite big_ord_recr big_ord0 /= setTI.
    rewrite -(setDKU (EU0 0%N)).
    rewrite /lebesgue_measure/=/lebesgue_stieltjes_measure/=/measure_extension/=.
    have /= Hle := outer_measureU2 ((wlength idfun)^*)%mu (U0_ 0%N `\` E) E.
    apply: (le_lt_trans Hle).
    apply: lte_add_pinfty => //.
    apply: (lt_trans (mU0E 0%N)).
    by rewrite ltry.
  apply/nonincreasing_seqP.
  move=> n.
  rewrite subsetEset.
  rewrite /U_.
  rewrite !bigcap_mkord.
  rewrite big_ord_recr /=.
  exact: subIsetl.
(* need definition of measurablity by equation between inner measure and outer measure? *)


have UooE: lebesgue_measure Uoo = (lebesgue_measure^* )%mu E.
  rewrite -(cvg_lim _ cvgUoo) //.
  apply: cvg_eq => //.
  rewrite -is_cvg_limn_esupE; last first.
    apply: ereal_nonincreasing_is_cvgn.
    apply/nonincreasing_seqP.
    admit.
  admit.


rewrite /measurable.
rewrite /=.
rewrite /measurableR.
rewrite /measurable.
rewrite /=.
Admitted.

(*
  ref:https://heil.math.gatech.edu/6337/spring11/section1.2.pdf
  Lemma 1.21
*)
Lemma outer_measure0_measurable (A : set R) :
   lebesgue_measure A = 0 -> measurable A.
Proof.
move=> A0.
apply: regularity_outer_lebesgue.
  by rewrite A0.
move=> e e0.
have := outer_regularity_outer A.
rewrite A0.
move/esym => inf0.
have : ereal_inf [set Z |
    exists X, [/\ Z = (lebesgue_measure) X, open X & A `<=` X]] \is a fin_num.
  by rewrite inf0.
move/(lb_ereal_inf_adherent e0).
move=> [] /= r [] U [] -> oU AU.
rewrite inf0 add0r => Ue.
exists U; split => //.
apply: (@le_lt_trans _ _ (lebesgue_measure U)).
  by rewrite le_outer_measure.
exact: Ue.
Qed.

Lemma outer_measure_Gdelta (A : set R) :
caratheodory_measurable lebesgue_measure A
  -> exists H, [/\ Gdelta H, A `<=` H & lebesgue_measure A = lebesgue_measure H].
Proof.
(* use lebesgue_regularity_outer? *)
Admitted.

(* TODO: move to lebesgue_measure.v *)
Lemma boundary_lebesgue_meausure0 (A : set R) :
  lebesgue_measure (A `\` (interior A)) = 0.
Proof.
Admitted.

Lemma caratheodory_measurableR_measurable (A : set R) :
caratheodory_measurable lebesgue_measure A
  -> measurable A.
Proof.
move=> cmA.
have := outer_measure_Gdelta cmA.
move=> [H [GdH AH muA]].
have mH : measurable H := Gdelta_measurable GdH.
rewrite -(@setDKU _ (interior A) A); last exact: interior_subset.
apply: measurableU; last first.
  apply: open_measurable.
  by apply: open_interior.
apply: outer_measure0_measurable.
exact: boundary_lebesgue_meausure0.
Qed.

(*
Lemma outer_measure0_measurable' (A : set R) : (lebesgue_measure^* )%mu A = 0 -> measurable A.
Proof.
move=> A0.
apply: caratheodory_measurableR_measurable.
apply: le_caratheodory_measurable => /= X.
suff -> : (lebesgue_measure^* )%mu (X `&` A) = 0.
  by rewrite add0r le_outer_measure //; apply: subIsetl.
apply/eqP; rewrite eq_le outer_measure_ge0 andbT.
by rewrite -A0 le_outer_measure //; apply: subIsetr.
Abort.
*)

Lemma lebesgue_measure_is_complete : measure_is_complete (@lebesgue_measure R).
Proof.
move=> /= A [/= N[mN N0 AN]].
apply: outer_measure0_measurable.
apply/eqP; rewrite eq_le measure_ge0 andbT.
rewrite -N0 le_measure ?inE //.
rewrite measurable_g_measurableTypeE /=.
Abort.

End lebesgue_measure_complete.

Section lusinN.
Context {R : realType}.
Let mu := @lebesgue_measure R.

Definition lusinN (A : set R) (f : R -> R) :=
  forall E, E `<=` A -> measurable E -> mu E = 0 -> mu (f @` E) = 0.

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

Local Notation mu := lebesgue_measure.

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
  measurable (`[f a, f b]%classic `\` increasing_points f).
Proof.
Abort.

Lemma nondecreasing_fun_image_Gdelta_measurable (f : R -> R) (Z : set R) :
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  Z `<=` `]a, b[%classic ->
  Gdelta Z ->
  measurable (f @` Z).
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
     = lebesgue_stieltjes_measure f cZ.
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
have ndt := (total_variation_nondecreasing bvf).
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


Lemma Banach_Zarecki_increasing (f : R -> R) :
  {within `[a, b], continuous f} ->
  {in `[a, b]  &, {homo f : x y / x <= y}} ->
  lusinN `[a, b] f ->
  abs_cont a b f.
Proof.
move=> cf incf lf; apply: contrapT => /existsNP[e0] /forallNP fe0.
have {fe0} : forall d : {posnum R},
    exists n, exists B : 'I_n -> R * R,
      [/\ (forall i, (B i).1 < (B i).2 /\ `](B i).1, (B i).2[ `<=` `[a, b]),
          trivIset setT (fun i => `](B i).1, (B i).2[%classic),
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
have ablt i t : (ab_ i t).1 < (ab_ i t).2.
  move: (projT2 (cid (ab_0 (delta_ i)))).
  by move=> [] /all_and2 [] => + _ _ _ _; apply.
have tab_ t : trivIset [set: 'I_(n_ t)]
    (fun i : 'I_(n_ t) => `](ab_ t i).1, (ab_ t i).2[%classic).
  move: (projT2 (cid (ab_0 (delta_ t)))).
  by case => _ + _ _ /=.
have d_prop i : \sum_(k < n_ i) (((ab_ i) k).2 - ((ab_ i) k).1) < delta_0 i.
  by rewrite /ab_; case: cid => ? [].
have e0_prop i : \sum_(k < n_ i) (f (((ab_ i) k).2) - f ((ab_ i) k).1) >= e0%:num.
  by rewrite /ab_; case: cid => ? [].
have H3 i k : (ab_ i k).1 < (ab_ i k).2 /\ `](ab_ i k).1, (ab_ i k).2[ `<=` `[a, b].
  by rewrite /ab_; case: cid => ? [].
pose E_ i := \big[setU/set0]_(k < n_ i) `](ab_ i k).1, (ab_ i k).2[%classic.
have mE i : measurable (E_ i) by exact: bigsetU_measurable.
pose G_ i := \bigcup_(j in [set j | (j >= i)%N]) E_ j.
have mG i : measurable (G_ i) by exact: bigcup_measurable.
pose A := \bigcap_i (G_ i).
have H2 : (@normr R _ 2^-1 < 1)%R by rewrite gtr0_norm// invf_lt1// ltr1n.
have H20 : 1 - 2^-1 != 0 :> R by rewrite lt0r_neq0// subr_gt0; apply: ltr_normlW.
have H1 : (@GRing.inv R 2) / (1 - 2^-1) = 1.
  by rewrite [X in X - _](splitr 1) div1r addrK divff.
have Eled n : (mu (E_ n) <= (delta_0 n)%:E)%E.
  rewrite measure_semi_additive_ord //=; last exact: bigsetU_measurable.
  apply/ltW.
  under eq_bigr do rewrite lebesgue_measure_itv/= lte_fin ifT // -EFinD.
  by rewrite sumEFin lte_fin; exact: d_prop.
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
          rewrite nneseries_addn; last by move=> i; by [].
          apply: measure_sigma_sub_additive.
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
        rewrite nneseries_addn; last by move=> i; apply: measure_ge0.
        rewrite [leRHS]nneseries_addn; last first.
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
      apply: measure_sigma_sub_additive => //; first exact: mG.
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
    by apply: (H3 _ _).2.
  + by apply: bigcapT_measurable => //.
  + exact: mA0.
have H n : (e0%:num%:E <= mu (f @` G_ n))%E.
  admit.
have fG_cvg : mu (f @` G_ n) @[n --> \oo] --> mu (f @` A).
  admit.
move/eqP : mfA0; apply/negP.
rewrite gt_eqF// (@lt_le_trans _ _ e0%:num%:E)//.
move/cvg_lim : (fG_cvg) => <- //.
apply: lime_ge.
  apply: ereal_nonincreasing_is_cvgn.
  move => n m nm.
  rewrite le_measure ?inE //.
  - (* by continuous? *)
    admit.
  - admit.
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
apply: Banach_Zarecki_increasing.
- exact: total_variation_continuous.
- exact: total_variation_nondecreasing.
- exact: Lusin_total_variation.
Qed.

End Banach_Zarecki.
