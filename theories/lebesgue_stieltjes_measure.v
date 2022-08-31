(* -*- company-coq-local-symbols: (("`&`" . ?∩) ("`|`" . ?∪) ("set0" . ?∅)); -*- *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
Require Import boolp reals ereal classical_sets signed topology numfun.
Require Import mathcomp_extra functions normedtype.
From HB Require Import structures.
Require Import sequences esum measure fsbigop cardinality set_interval.
Require Import realfun.
<<<<<<< abs_cont_measure
=======
Require Import lebesgue_integral.
>>>>>>> abs_cont_measure

(******************************************************************************)
(*                       Lebesgue Stieltjes Measure                           *)
(*                                                                            *)
(* This file contains a formalization of the Lebesgue-Stieltjes measure using *)
(* the Extension theorem available in measure.v.                              *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* TODO: move *)
Notation right_continuous f :=
  (forall x, f%function @ at_right x --> f%function x).

Lemma nondecreasing_right_continuousP (R : realType) (a : R) (e : R)
    (f : R -> R) (ndf : {homo f : x y / x <= y}) (rcf : (right_continuous f)) :
  e > 0 -> exists d : {posnum R}, f (a + d%:num) <= f a + e.
Proof.
move=> e0; move: rcf => /(_ a)/(@cvg_dist _ [normedModType R of R^o]).
move=> /(_ _ e0)[] _ /posnumP[d] => h.
exists (PosNum [gt0 of (d%:num / 2)]) => //=.
move: h => /(_ (a + d%:num / 2)) /=.
rewrite opprD addrA subrr distrC subr0 ger0_norm //.
rewrite ltr_pdivr_mulr// ltr_pmulr// ltr1n => /(_ erefl).
rewrite ltr_addl divr_gt0// => /(_ erefl).
rewrite ler0_norm; last by rewrite subr_le0 ndf// ler_addl.
by rewrite opprB ltr_subl_addl => fa; exact: ltW.
Qed.

(* TODO: move and use in lebesgue_measure.v? *)
Lemma le_inf (R : realType) (S1 S2 : set R) :
  -%R @` S2 `<=` down (-%R @` S1) -> nonempty S2 -> has_inf S1
    -> (inf S1 <= inf S2)%R.
Proof.
move=> S21 S12 S1i; rewrite ler_oppl opprK le_sup// ?has_inf_supN//.
exact/nonemptyN.
Qed.

Definition EFinf {R : numDomainType} (f : R -> R) : \bar R -> \bar R :=
  fun x => if x is r%:E then (f r)%:E else x.

Lemma nondecreasing_EFinf (R : realDomainType) (f : R -> R) :
  {homo f : x y / (x <= y)%R} -> {homo EFinf f : x y / (x <= y)%E}.
Proof.
move=> ndf.
by move=> [r| |] [l| |]//=; rewrite ?leey ?leNye// !lee_fin; exact: ndf.
Qed.

Section hlength.
Local Open Scope ereal_scope.
Variables (R : realType) (f : R -> R).
Hypothesis ndf : {homo f : x y / (x <= y)%R}.

Let g : \bar R -> \bar R := EFinf f.

Implicit Types i j : interval R.
Definition itvs : Type := R.

Definition hlength (A : set itvs) : \bar R := let i := Rhull A in g i.2 - g i.1.

Lemma hlength0 : hlength (set0 : set R) = 0.
Proof. by rewrite /hlength Rhull0 /= subee. Qed.

Lemma hlength_singleton (r : R) : hlength `[r, r] = 0.
Proof.
rewrite /hlength /= asboolT// sup_itvcc//= asboolT//.
by rewrite asboolT inf_itvcc//= ?subee// inE.
Qed.

Lemma hlength_itv i : hlength [set` i] = if i.2 > i.1 then g i.2 - g i.1 else 0.
Proof.
case: ltP => [/lt_ereal_bnd/neitvP i12|]; first by rewrite /hlength set_itvK.
rewrite le_eqVlt => /orP[|/lt_ereal_bnd i12]; last first.
  rewrite -hlength0; congr (hlength _).
  by apply/eqP/negPn; rewrite -/(neitv _) neitvE -leNgt (ltW i12).
case: i => -[ba a|[|]] [bb b|[|]] //=.
- rewrite /= => /eqP[->{b}]; move: ba bb => -[] []; try
    by rewrite set_itvE hlength0.
  by rewrite hlength_singleton.
- by move=> _; rewrite set_itvE hlength0.
- by move=> _; rewrite set_itvE hlength0.
Qed.

Lemma hlength_setT : hlength setT = +oo%E :> \bar R.
Proof. by rewrite /hlength RhullT. Qed.

Lemma hlength_finite_fin_num i : neitv i -> hlength [set` i] < +oo ->
  ((i.1 : \bar R) \is a fin_num) /\ ((i.2 : \bar R) \is a fin_num).
Proof.
move: i => [[ba a|[]] [bb b|[]]] /neitvP //=; do ?by rewrite ?set_itvE ?eqxx.
by move=> _; rewrite hlength_itv /= ltey.
by move=> _; rewrite hlength_itv /= ltNye.
by move=> _; rewrite hlength_itv.
Qed.

Lemma finite_hlengthE i : neitv i -> hlength [set` i] < +oo ->
  hlength [set` i] = (fine (g i.2))%:E - (fine (g i.1))%:E.
Proof.
move=> i0 ioo; have [i1f i2f] := hlength_finite_fin_num i0 ioo.
rewrite fineK; last first.
  by rewrite /g; move: i2f; case: (ereal_of_itv_bound i.2).
rewrite fineK; last first.
  by rewrite /g; move: i1f; case: (ereal_of_itv_bound i.1).
rewrite hlength_itv; case: ifPn => //; rewrite -leNgt le_eqVlt => /predU1P[->|].
  by rewrite subee// /g; move: i1f; case: (ereal_of_itv_bound i.1).
by move/lt_ereal_bnd/ltW; rewrite leNgt; move: i0 => /neitvP => ->.
Qed.

Lemma hlength_itv_bnd (a b : R) (x y : bool): (a <= b)%R ->
  hlength [set` Interval (BSide x a) (BSide y b)] = (f b - f a)%:E.
Proof.
move=> ab; rewrite hlength_itv/= lte_fin lt_neqAle ab andbT.
by have [-> /=|/= ab'] := eqVneq a b; rewrite ?subrr// EFinN EFinB.
Qed.

Lemma hlength_infty_bnd b r :
  hlength [set` Interval -oo%O (BSide b r)] = +oo :> \bar R.
Proof. by rewrite hlength_itv /= ltNye. Qed.

Lemma hlength_bnd_infty b r :
  hlength [set` Interval (BSide b r) +oo%O] = +oo :> \bar R.
Proof. by rewrite hlength_itv /= ltey. Qed.

Lemma pinfty_hlength i : hlength [set` i] = +oo ->
  (exists s r, i = Interval -oo%O (BSide s r) \/ i = Interval (BSide s r) +oo%O)
  \/ i = `]-oo, +oo[.
Proof.
rewrite hlength_itv; case: i => -[ba a|[]] [bb b|[]] //= => [|_|_|].
- by case: ifPn.
- by left; exists ba, a; right.
- by left; exists bb, b; left.
- by right.
Qed.

Lemma hlength_ge0 i : 0 <= hlength [set` i].
Proof.
rewrite hlength_itv; case: ifPn => //; case: (i.1 : \bar _) => [r| |].
- by rewrite suber_ge0// => /ltW /(nondecreasing_EFinf ndf).
- by rewrite ltNge leey.
- by case: (i.2 : \bar _) => //= [r _]; rewrite leey.
Qed.
Local Hint Extern 0 (0%:E <= hlength _) => solve[apply: hlength_ge0] : core.

Lemma hlength_Rhull (A : set R) : hlength [set` Rhull A] = hlength A.
Proof. by rewrite /hlength Rhull_involutive. Qed.

Lemma le_hlength_itv i j :
  {subset i <= j} -> hlength [set` i] <= hlength [set` j].
Proof.
set I := [set` i]; set J := [set` j].
have [->|/set0P I0] := eqVneq I set0; first by rewrite hlength0 hlength_ge0.
have [J0|/set0P J0] := eqVneq J set0.
  by move/subset_itvP; rewrite -/J J0 subset0 -/I => ->.
move=> /subset_itvP ij; apply: lee_sub => /=.
  have [ui|ui] := asboolP (has_ubound I).
    have [uj /=|uj] := asboolP (has_ubound J); last by rewrite leey.
    rewrite lee_fin; apply: ndf; apply/le_sup => //.
    by move=> r Ir; exists r; split => //; apply: ij.
  have [uj /=|//] := asboolP (has_ubound J).
  by move: ui; have := subset_has_ubound ij uj.
have [lj /=|lj] := asboolP (has_lbound J); last by rewrite leNye.
have [li /=|li] := asboolP (has_lbound I); last first.
  by move: li; have := subset_has_lbound ij lj.
rewrite lee_fin; apply/ndf/le_inf => //.
move=> r [r' Ir' <-{r}]; exists (- r')%R.
by split => //; exists r' => //; apply: ij.
Qed.

Lemma le_hlength : {homo hlength : A B / A `<=` B >-> A <= B}.
Proof.
move=> a b /le_Rhull /le_hlength_itv.
by rewrite (hlength_Rhull a) (hlength_Rhull b).
Qed.

End hlength.
Arguments hlength {R}.
#[global] Hint Extern 0 (0%:E <= hlength _) => solve[apply: hlength_ge0] : core.

Section itv_semiRingOfSets.
Variable R : realType.
Implicit Types (I J K : set R).
Definition ocitv_type : Type := R.

Definition ocitv := [set `]x.1, x.2]%classic | x in [set: R * R]].

Lemma is_ocitv a b : ocitv `]a, b]%classic.
Proof. by exists (a, b); split => //=; rewrite in_itv/= andbT. Qed.
Hint Extern 0 (ocitv _) => solve [apply: is_ocitv] : core.

Lemma ocitv0 : ocitv set0.
Proof. by exists (1, 0); rewrite //= set_itv_ge ?bnd_simp//= ltr10. Qed.
Hint Resolve ocitv0 : core.

Lemma ocitvP X : ocitv X <-> X = set0 \/ exists2 x, x.1 < x.2 & X = `]x.1, x.2]%classic.
Proof.
split=> [[x _ <-]|[->//|[x xlt ->]]]//.
case: (boolP (x.1 < x.2)) => x12; first by right; exists x.
by left; rewrite set_itv_ge.
Qed.

Lemma ocitvD : semi_setD_closed ocitv.
Proof.
move=> _ _ [a _ <-] /ocitvP[|[b ltb]] ->.
  rewrite setD0; exists [set `]a.1, a.2]%classic].
  by split=> [//|? ->//||? ? -> ->//]; rewrite bigcup_set1.
rewrite setDE setCitv/= setIUr -!set_itvI.
rewrite /Order.meet/= /Order.meet/= /Order.join/=
         ?(andbF, orbF)/= ?(meetEtotal, joinEtotal).
rewrite -negb_or le_total/=; set c := minr _ _; set d := maxr _ _.
have inside : a.1 < c -> d < a.2 -> `]a.1, c] `&` `]d, a.2] = set0.
  rewrite -subset0 lt_minr lt_maxl => /andP[a12 ab1] /andP[_ ba2] x /= [].
  have b1a2 : b.1 <= a.2 by rewrite ltW// (lt_trans ltb).
  have a1b2 : a.1 <= b.2 by rewrite ltW// (lt_trans _ ltb).
  rewrite /c /d (min_idPr _)// (max_idPr _)// !in_itv /=.
  move=> /andP[a1x xb1] /andP[b2x xa2].
  by have := lt_le_trans b2x xb1; case: ltgtP ltb.
exists ((if a.1 < c then [set `]a.1, c]%classic] else set0) `|`
        (if d < a.2 then [set `]d, a.2]%classic] else set0)); split.
- by rewrite finite_setU; do! case: ifP.
- by move=> ? []; case: ifP => ? // ->//=.
- by rewrite bigcup_setU; congr (_ `|` _);
     case: ifPn => ?; rewrite ?bigcup_set1 ?bigcup_set0// set_itv_ge.
- move=> I J/=; case: ifP => //= ac; case: ifP => //= da [] // -> []// ->.
    by rewrite inside// => -[].
  by rewrite setIC inside// => -[].
Qed.

Lemma ocitvI : setI_closed ocitv.
Proof.
move=> _ _ [a _ <-] [b _ <-]; rewrite -set_itvI/=.
rewrite /Order.meet/= /Order.meet /Order.join/=
        ?(andbF, orbF)/= ?(meetEtotal, joinEtotal).
by rewrite -negb_or le_total/=.
Qed.

Variable d : measure_display.

HB.instance Definition _ :=
  @isSemiRingOfSets.Build d ocitv_type (Pointed.class R) ocitv ocitv0 ocitvI ocitvD.

Definition itvs_semiRingOfSets := [the semiRingOfSetsType d of ocitv_type].

Variable f : R -> R.

Lemma hlength_semi_additive : semi_additive (hlength f : set ocitv_type -> _).
Proof.
move=> /= I n /(_ _)/cid2-/all_sig[b]/all_and2[_]/(_ _)/esym-/funext {I}->.
move=> Itriv [[/= a1 a2] _] /esym /[dup] + ->.
rewrite hlength_itv ?lte_fin/= -EFinB.
case: ifPn => a12; last first.
  pose I i :=  `](b i).1, (b i).2]%classic.
  rewrite set_itv_ge//= -(bigcup_mkord _ I) /I => /bigcup0P I0.
  by under eq_bigr => i _ do rewrite I0//= hlength0; rewrite big1.
set A := `]a1, a2]%classic.
rewrite -bigcup_pred; set P := xpredT; rewrite (eq_bigl P)//.
move: P => P; have [p] := ubnP #|P|; elim: p => // p IHp in P a2 a12 A *.
rewrite ltnS => cP /esym AE.
have : A a2 by rewrite /A /= in_itv/= lexx andbT.
rewrite AE/= => -[i /= Pi] a2bi.
case: (boolP ((b i).1 < (b i).2)) => bi; last by rewrite itv_ge in a2bi.
have {}a2bi : a2 = (b i).2.
  apply/eqP; rewrite eq_le (itvP a2bi)/=.
  suff: A (b i).2 by move=> /itvP->.
  by rewrite AE; exists i=> //=; rewrite in_itv/= lexx andbT.
rewrite {a2}a2bi in a12 A AE *.
rewrite (bigD1 i)//= hlength_itv ?lte_fin/= bi !EFinD -addeA.
congr (_ + _)%E; apply/eqP; rewrite addeC -sube_eq// 1?adde_defC//.
rewrite ?EFinN oppeK addeC; apply/eqP.
case: (eqVneq a1 (b i).1) => a1bi.
  rewrite {a1}a1bi in a12 A AE {IHp} *; rewrite subee ?big1// => j.
  move=> /andP[Pj Nji]; rewrite hlength_itv ?lte_fin/=; case: ifPn => bj//.
  exfalso; have /trivIsetP/(_ j i I I Nji) := Itriv.
  pose m := ((b j).1 + (b j).2) / 2%:R.
  have mbj : `](b j).1, (b j).2]%classic m.
     by rewrite /= !in_itv/= ?(midf_lt, midf_le)//= ltW.
  rewrite -subset0 => /(_ m); apply; split=> //.
  by suff: A m by []; rewrite AE; exists j => //.
have a1b2 j : P j -> (b j).1 < (b j).2 -> a1 <= (b j).2.
  move=> Pj bj; suff /itvP-> : A (b j).2 by [].
  by rewrite AE; exists j => //=; rewrite ?in_itv/= bj//=.
have a1b j : P j -> (b j).1 < (b j).2 -> a1 <= (b j).1.
  move=> Pj bj; case: ltP=> // bj1a.
  suff : A a1 by rewrite /A/= in_itv/= ltxx.
  by rewrite AE; exists j; rewrite //= in_itv/= bj1a//= a1b2.
have bbi2 j : P j -> (b j).1 < (b j).2 -> (b j).2 <= (b i).2.
  move=> Pj bj; suff /itvP-> : A (b j).2 by [].
  by rewrite AE; exists j => //=; rewrite ?in_itv/= bj//=.
apply/IHp.
- by rewrite lt_neqAle a1bi/= a1b.
- rewrite (leq_trans _ cP)// -(cardID (pred1 i) P).
  rewrite [X in (_ < X + _)%N](@eq_card _ _ (pred1 i)); last first.
    by move=> j; rewrite !inE andbC; case: eqVneq => // ->.
  rewrite ?card1 ?ltnS// subset_leq_card//.
  by apply/fintype.subsetP => j; rewrite -topredE/= !inE andbC.
apply/seteqP; split=> /= [x [j/= /andP[Pj Nji]]|x/= xabi].
  case: (boolP ((b j).1 < (b j).2)) => bj; last by rewrite itv_ge.
  apply: subitvP; rewrite subitvE ?bnd_simp a1b//= leNgt.
  have /trivIsetP/(_ j i I I Nji) := Itriv.
  rewrite -subset0 => /(_ (b j).2); apply: contra_notN => /= bi1j2.
  by rewrite !in_itv/= bj !lexx bi1j2 bbi2.
have: A x.
  rewrite /A/= in_itv/= (itvP xabi)/= ltW//.
  by rewrite (le_lt_trans _ bi) ?(itvP xabi).
rewrite AE => -[j /= Pj xbj].
exists j => //=.
apply/andP; split=> //; apply: contraTneq xbj => ->.
by rewrite in_itv/= le_gtF// (itvP xabi).
Qed.

Hint Extern 0 (measurable _) => solve [apply: is_ocitv] : core.

Lemma hlength_sigma_finite : sigma_finite [set: ocitv_type] (hlength f).
Proof.
exists (fun k : nat => `] (- k%:R)%R, k%:R]%classic).
  apply/esym; rewrite -subTset => /= x _ /=.
  exists `|(floor `|x|%R + 1)%R|%N; rewrite //= in_itv/=.
  rewrite !natr_absz intr_norm intrD -RfloorE.
  suff: `|x| < `|Rfloor `|x| + 1| by rewrite ltr_norml => /andP[-> /ltW->].
  rewrite [ltRHS]ger0_norm//.
    by rewrite (le_lt_trans _ (lt_succ_Rfloor _))// ?ler_norm.
  by rewrite addr_ge0// -Rfloor0 le_Rfloor.
by move=> k; split => //; rewrite hlength_itv /= -EFinB; case: ifP; rewrite ltey.
Qed.

Hypothesis ndf : {homo f : x y / (x <= y)%R}.

Lemma hlength_ge0' (I : set ocitv_type) : (0 <= hlength f I)%E.
Proof. by rewrite -(hlength0 f) le_hlength. Qed.

HB.instance Definition _ :=
  isAdditiveMeasure.Build _ R _ (hlength f : set ocitv_type -> _)
    hlength_ge0' hlength_semi_additive.

Lemma hlength_content_sub_fsum (D : {fset nat}) a0 b0
    (a b : nat -> R) : (forall i, i \in D -> a i <= b i) ->
    `]a0, b0] `<=` \big[setU/set0]_(i <- D) `] a i, b i]%classic ->
  f b0 - f a0 <= \sum_(i <- D) (f (b i) - f (a i)).
Proof.
move=> Dab h; have [ab|ab] := leP a0 b0; last first.
  apply (@le_trans _ _ 0); first by rewrite subr_le0 ndf// ltW.
  by rewrite big_seq sumr_ge0// => i iD; rewrite subr_ge0 ndf// Dab.
have mab k :
  [set` D] k -> @measurable d itvs_semiRingOfSets `]a k, b k]%classic by [].
move: h; rewrite -bigcup_fset.
move/(@content_sub_fsum d R _
    [the additive_measure _ _ of hlength f : set ocitv_type -> _] _ [set` D]
    `]a0, b0]%classic (fun x => `](a x), (b x)]%classic) (finite_fset D) mab
  (is_ocitv _ _)) => /=.
rewrite hlength_itv_bnd// -lee_fin => /le_trans; apply.
rewrite -sumEFin fsbig_finite//= set_fsetK// big_seq [in X in (_ <= X)%E]big_seq.
by apply: lee_sum => i iD; rewrite hlength_itv_bnd// Dab.
Qed.

Lemma hlength_sigma_sub_additive (rcf : right_continuous f) :
  sigma_sub_additive (hlength f : set ocitv_type -> _).
Proof.
move=> I A /(_ _)/cid2-/all_sig[b]/all_and2[_]/(_ _)/esym AE.
move=> [a _ <-]; rewrite hlength_itv ?lte_fin/= -EFinB => lebig.
case: ifPn => a12; last first.
  rewrite nneseries_esum; last by move=> ? _; exact: hlength_ge0'.
  by rewrite esum_ge0// => ? _; exact: hlength_ge0'.
wlog wlogh : b A AE lebig / forall n, (b n).1 <= (b n).2.
  move=> /= h.
  set A' := fun n => if (b n).1 >= (b n).2 then set0 else A n.
  set b' := fun n => if (b n).1 >= (b n).2 then (0, 0) else b n.
  rewrite [X in (_ <= X)%E](_ : _ = \sum_(n <oo) hlength f (A' n))%E; last first.
    apply: (@eq_nneseries _ (hlength f \o A) (hlength f \o A')) => k.
    rewrite /= /A' AE; case: ifPn => // bn.
    by rewrite set_itv_ge//= bnd_simp -leNgt.
  apply (h b').
  - move=> k; rewrite /A'; case: ifPn => // bk.
    by rewrite set_itv_ge//= bnd_simp -leNgt /b' bk.
  - by rewrite AE /b' (negbTE bk).
  - apply: (subset_trans lebig); apply subset_bigcup => k _.
    rewrite /A' AE; case: ifPn => bk //.
    by rewrite subset0 set_itv_ge//= bnd_simp -leNgt.
  - by move=> k; rewrite /b'; case: ifPn => //; rewrite -ltNge => /ltW.
apply: lee_adde => e.
rewrite [e%:num]splitr [in leRHS]EFinD addeA -lee_subl_addr//.
apply: le_trans (epsilon_trick _ _ _) => //=.
have [c ce] := nondecreasing_right_continuousP a.1 ndf rcf [gt0 of e%:num / 2].
have [D De] : exists D : nat -> {posnum R}, forall i,
    f ((b i).2 + (D i)%:num) <= f ((b i).2) + (e%:num / 2) / 2 ^ i.+1.
  suff : forall i, exists di : {posnum R},
      f ((b i).2 + di%:num) <= f ((b i).2) + (e%:num / 2) / 2 ^ i.+1.
    by move/choice => -[g hg]; exists g.
  move=> k; apply nondecreasing_right_continuousP => //.
  by rewrite divr_gt0 // exprn_gt0.
have acbd : `[ a.1 + c%:num / 2, a.2] `<=` \bigcup_i `](b i).1, (b i).2 + (D i)%:num[%classic.
  apply (@subset_trans _ `]a.1, a.2]).
    move=> r; rewrite /= !in_itv/= => /andP [+ ->].
    by rewrite andbT; apply: lt_le_trans; rewrite ltr_addl.
  apply (subset_trans lebig) => r [n _ Anr]; exists n => //.
  move: Anr; rewrite AE /= !in_itv/= => /andP [->]/= /le_lt_trans.
  by apply; rewrite ltr_addl.
have := @segment_compact _ (a.1 + c%:num / 2) a.2; rewrite compact_cover.
have obd k : [set: nat] k-> open `](b k).1, ((b k).2 + (D k)%:num)[%classic.
  by move=> _; exact: interval_open.
move=> /(_ _ _ _ obd acbd){obd acbd}.
case=> X _ acXbd.
rewrite -EFinD.
apply: (@le_trans _ _ (\sum_(i <- X) (hlength f `](b i).1, (b i).2]%classic) +
                       \sum_(i <- X) (f ((b i).2 + (D i)%:num)%R - f (b i).2)%:E)%E).
  apply: (@le_trans _ _ (f a.2 - f (a.1 + c%:num / 2))%:E).
    rewrite lee_fin -addrA -opprD ler_sub// (le_trans _ ce)// ndf//.
    by rewrite ler_add2l ler_pdivr_mulr// ler_pmulr// ler1n.
  apply: (@le_trans _ _ (\sum_(i <- X) (f ((b i).2 + (D i)%:num) - f (b i).1)%:E)%E).
    rewrite sumEFin lee_fin hlength_content_sub_fsum//.
      by move=> k kX; rewrite (@le_trans _ _ (b k).2)// ler_addl.
    apply: subset_trans.
      exact/(subset_trans _ acXbd)/subset_itv_oc_cc.
    move=> x [k kX] kx; rewrite -bigcup_fset; exists k => //.
    by move: x kx; exact: subset_itv_oo_oc.
  rewrite addeC -big_split/=; apply: lee_sum => k _.
  by rewrite !(EFinB, hlength_itv_bnd)// addeA subeK.
rewrite -big_split/= nneseries_esum//; last first.
  by move=> k _; rewrite adde_ge0// hlength_ge0'.
<<<<<<< abs_cont_measure
rewrite esum_ge//; exists [set` X] => //; rewrite fsbig_finite// ?set_fsetK//=.
rewrite lee_sum // => k _; rewrite ?AE// !hlength_itv/= ?lte_fin -?EFinD/=.
by case: ifPn => ?; rewrite ?add0e ?lee_add2l// lee_fin ler_subl_addl natrX De.
=======
rewrite esum_ge//; exists X => //.
rewrite big_seq [in X in (_ <= X)%E]big_seq; apply: lee_sum => k kX.
by rewrite AE lee_add2l// lee_fin ler_subl_addl natrX De.
>>>>>>> abs_cont_measure
Qed.

Let gitvs := [the measurableType _ of salgebraType ocitv].

Definition lebesgue_stieltjes_measure :=
  Hahn_ext [the additive_measure _ _ of hlength f : set ocitv_type -> _ ].

Variable rcf : right_continuous f.

Let lebesgue_stieltjes_measure0 : lebesgue_stieltjes_measure set0 = 0%E.
Proof. by []. Qed.

Let lebesgue_stieltjes_measure_ge0 : forall x, (0 <= lebesgue_stieltjes_measure x)%E.
Proof. exact: measure.Hahn_ext_ge0. Qed.

Let lebesgue_stieltjes_measure_semi_sigma_additive : semi_sigma_additive lebesgue_stieltjes_measure.
Proof. exact/measure.Hahn_ext_sigma_additive/hlength_sigma_sub_additive. Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ lebesgue_stieltjes_measure
  lebesgue_stieltjes_measure0 lebesgue_stieltjes_measure_ge0 lebesgue_stieltjes_measure_semi_sigma_additive.

End itv_semiRingOfSets.
Arguments lebesgue_stieltjes_measure {R}.

Section lebesgue_stieltjes_measure_itv.
Variables (d : measure_display) (R : realType) (f : R -> R).
Hypotheses (ndf : {homo f : x y / x <= y}) (rcf : right_continuous f).

Let m := lebesgue_stieltjes_measure d f ndf.

Let g : \bar R -> \bar R := EFinf f.

Let lebesgue_stieltjes_measure_itvoc (a b : R) :
  (m `]a, b] = hlength f `]a, b])%classic.
Proof.
rewrite /m /lebesgue_stieltjes_measure /= /Hahn_ext measurable_mu_extE//; last first.
  by exists (a, b).
exact: hlength_sigma_sub_additive.
Qed.

Lemma set1Ebigcap (x : R) : [set x] = \bigcap_k `](x - k.+1%:R^-1)%R, x]%classic.
Proof.
apply/seteqP; split => [_ -> k _ /=|].
  by rewrite in_itv/= lexx andbT ltr_subl_addl ltr_addr invr_gt0.
move=> y h; apply/eqP/negPn/negP => yx.
red in h.
simpl in h.
<<<<<<< abs_cont_measure
Abort.
=======
Admitted.
>>>>>>> abs_cont_measure

Let lebesgue_stieltjes_measure_set1 (a : R) :
  m [set a] = ((f a)%:E - (lim (f @ at_left a))%:E)%E.
Proof.
<<<<<<< abs_cont_measure
(*rewrite (set1Ebigcap a).*)
Abort.
=======
rewrite (set1Ebigcap a).
Admitted.
>>>>>>> abs_cont_measure

Let lebesgue_stieltjes_measure_itvoo (a b : R) : a <= b ->
  m `]a, b[%classic = ((lim (f @ at_left b))%:E - (f a)%:E)%E.
Proof.
<<<<<<< abs_cont_measure
Abort.
=======
Admitted.
>>>>>>> abs_cont_measure

Let lebesgue_stieltjes_measure_itvcc (a b : R) : a <= b ->
  m `[a, b]%classic = ((f b)%:E - (lim (f @ at_left a))%:E)%E.
Proof.
<<<<<<< abs_cont_measure
Abort.
=======
Admitted.
>>>>>>> abs_cont_measure

Let lebesgue_stieltjes_measure_itvco (a b : R) : a <= b ->
  m `[a, b[%classic = ((lim (f @ at_left b))%:E - (lim (f @ at_left a))%:E)%E.
Proof.
<<<<<<< abs_cont_measure
Abort.
=======
Admitted.
>>>>>>> abs_cont_measure


End lebesgue_stieltjes_measure_itv.

Definition abs_continuous d (T : measurableType d) (R : realType)
    (m1 m2 : set T -> \bar R) :=
  forall A : set T, measurable A -> (m2 A = 0)%E -> (m1 A = 0)%E.

 Notation "m1 `<< m2" := (abs_continuous m1 m2) (at level 51).

Section dependent_choice_Type.
Variables (X : Type) (R : X -> X -> Prop).

Lemma dependent_choice_Type : (forall x : X, {y | R x y}) ->
  forall x0, {f : nat -> X | f O = x0 /\ forall n, R (f n) (f n.+1)}.
Proof.
move=> h x0.
set (f := fix f n := if n is n'.+1 then proj1_sig (h (f n')) else x0).
exists f; split => //.
intro n; induction n; simpl; apply proj2_sig.
Qed.
End dependent_choice_Type.

HB.mixin Record isFiniteSignedMeasure d (R : numFieldType)
  (T : semiRingOfSetsType d) (mu : set T -> \bar R) := {
    isfinite : forall U, measurable U -> mu U \is a fin_num}.

HB.mixin Record isAdditiveSignedMeasure d
    (R : numFieldType) (T : semiRingOfSetsType d) (mu : set T -> \bar R) := {
  smeasure_semi_additive : semi_additive mu }.

HB.structure Definition AdditiveSignedMeasure d
    (R : numFieldType) (T : semiRingOfSetsType d) := {
  mu of isAdditiveSignedMeasure d R T mu & isFiniteSignedMeasure d R T mu}.

Notation additive_smeasure := AdditiveSignedMeasure.type.
Notation "{ 'additive_smeasure' 'set' T '->' '\bar' R }" :=
  (additive_smeasure R T) (at level 36, T, R at next level,
    format "{ 'additive_smeasure'  'set'  T  '->'  '\bar'  R }") : ring_scope.

HB.mixin Record isSignedMeasure0 d
    (R : numFieldType) (T : semiRingOfSetsType d)
    (mu : set T -> \bar R) := {
  smeasure_semi_sigma_additive : semi_sigma_additive mu }.

HB.structure Definition SignedMeasure d
    (R : numFieldType) (T : semiRingOfSetsType d) :=
  {mu of isSignedMeasure0 d R T mu & AdditiveSignedMeasure d mu}.

Notation smeasure := SignedMeasure.type.
Notation "{ 'smeasure' 'set' T '->' '\bar' R }" := (smeasure R T)
  (at level 36, T, R at next level,
    format "{ 'smeasure'  'set'  T  '->'  '\bar'  R }") : ring_scope.

Lemma ndidR (R : realType) : {homo (@idfun R) : x y / x <= y}.
Proof.
move=> x y /=.
done.
Qed.

Lemma continuous_right_continuous (R : realType) (f : R -> R)
  : continuous f -> right_continuous f.
Proof.
move=> cf.
move=> x/=.
rewrite/at_right.
apply: cvg_within_filter.
apply/cf.
Qed.

Lemma rcidR (R : realType) : right_continuous (@idfun R).
Proof.
apply/continuous_right_continuous.
move=> x.
exact: cvg_id.
Qed.

Definition lebesgue_measure d (R : realType) := lebesgue_stieltjes_measure d (@idfun R) (@ndidR R) (* (@rcidR R) *).

(*
Definition abs_continuous_function_over_R d (R : realType) (f : R -> R)
    (ndf : {homo f : x y / x <= y}) (rcf : right_continuous f)
  := abs_continuous (lebesgue_stieltjes_measure d f ndf rcf) (lebesgue_measure R).
*)

(* maybe rewrite I : R * R to I : interval R *)
Definition abs_continuous_function (R : realType) (f : R -> R) (I : R * R)
    := forall e : {posnum R}, exists d : {posnum R},
         forall J : nat -> R * R, forall n : nat,
           \sum_(k < n)((J k).2 - (J k).1) < d%:num ->
             trivIset setT (fun n => `[(J n).1, (J n).2]%classic) ->
               (forall n, I.1 <= (J n).1 /\ (J n).2 <= I.2 ) ->
                 \sum_(k < n) `| f (J k).2 - f (J k).1 | < e%:num.

Definition positive_set d (R : realType) (X : measurableType d)
             (nu : {smeasure set X -> \bar R}) (P : set X):=
               (P \in measurable) /\
                 forall E, (E \in measurable) -> (E `<=` P) -> (nu E >= 0)%E.
Definition negative_set d (R : realType) (X : measurableType d)
             (nu : {smeasure set X -> \bar R}) (N : set X):=
               (N \in measurable) /\
                 forall E, (E \in measurable) -> (E `<=` N) -> (nu E <= 0)%E.

Lemma subset_nonnegative_set d (R : realType) (X : measurableType d)
             (nu : {smeasure set X -> \bar R}) (N M : set X) : (M `<=` N) ->
              (nu N < 0)%E -> (nu M > 0)%E -> (~ negative_set nu N) -> (~ negative_set nu (N `\` M)).
<<<<<<< abs_cont_measure
Abort.
=======
Admitted.
>>>>>>> abs_cont_measure

Local Open Scope ereal_scope.

Lemma s_semi_additiveW d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}) : mu set0 = 0 -> semi_additive mu -> semi_additive2 mu.
Proof.
move=> mu0 amx A B mA mB + AB; rewrite -bigcup2inE bigcup_mkord.
move=> /(amx (bigcup2 A B))->.
- by rewrite !(big_ord_recl, big_ord0)/= adde0.
- by move=> [|[|[]]]//=.
- move=> [|[|i]] [|[|j]]/= _ _ //.
  + rewrite AB.
    by case.
  + rewrite setI0.
    by case.
  + rewrite setIC.
    rewrite AB.
    by case.
  + rewrite setI0.
    by case.
  + rewrite set0I.
    by case.
  + rewrite set0I.
    by case.
  + rewrite setI0.
    by case.
Qed.

Lemma s_measure0 d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}): mu set0 = 0.
Proof.
have /[!big_ord0] ->// := @smeasure_semi_additive _ _ _ mu (fun=> set0) 0%N.
exact: trivIset_set0.
Qed.


Hint Resolve s_measure0 : core.

Hint Resolve smeasure_semi_additive : core.

Lemma s_semi_additive2E d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}) : semi_additive2 mu = additive2 mu.
Proof.
rewrite propeqE; split=> [amu A B ? ? ?|amu A B ? ? _ ?]; last by rewrite amu.
by rewrite amu //; exact: measurableU.
Qed.

Lemma s_measure_semi_additive2 d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}) : semi_additive2 mu.
Proof. apply: s_semi_additiveW => //. Qed.
#[global] Hint Resolve s_measure_semi_additive2 : core.

Lemma s_measureU d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}) : additive2 mu.
Proof. by rewrite -s_semi_additive2E. Qed.

Lemma s_measureDI d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}) (A B : set X) : measurable A -> measurable B ->
  mu A = mu (A `\` B) + mu (A `&` B).
Proof.
move=> mA mB; rewrite -s_measure_semi_additive2.
- by rewrite -setDDr setDv setD0.
- exact: measurableD.
- exact: measurableI.
- by apply: measurableU; [exact: measurableD |exact: measurableI].
- by rewrite setDE setIACA setICl setI0.
Qed.

<<<<<<< abs_cont_measure
=======
Lemma lte_ninfty_eq (R : realDomainType) (x : \bar R) :
   (-oo < x) = (x \is a fin_num) || (x == +oo).
Proof.
Admitted.

>>>>>>> abs_cont_measure
Lemma s_measureD d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}) (A B : set X) :
  measurable A -> measurable B ->
    (*mu A < +oo ->*) mu (A `\` B) = mu A - mu (A `&` B).
Proof.
move=> mA mB.
rewrite (s_measureDI mu mA mB) addeK// fin_numE 1?gt_eqF 1?lt_eqF//.
<<<<<<< abs_cont_measure
- rewrite ltey_eq.
  rewrite isfinite //.
  exact:measurableI.
- rewrite ltNye_eq.
=======
- rewrite lte_pinfty_eq.
  rewrite isfinite //.
  exact:measurableI.
- rewrite lte_ninfty_eq.
>>>>>>> abs_cont_measure
  rewrite isfinite//.
  exact:measurableI.
Qed.

<<<<<<< abs_cont_measure
Lemma inv_cvg (R : realType) (u : R ^nat) :
  (forall n, 0 < u n)%R ->
  (fun n => (u n)^-1) --> (0 : R)%R -> u --> +oo%R.
Proof.
move=> u0 uV0; apply/cvgPpinfty => M.
move/(@cvg_distP _ [normedModType R of R^o]) : uV0 => /(_ (`|M| + 1)^-1%R).
rewrite invr_gt0 ltr_paddl// => /(_ erefl); rewrite !near_map.
apply: filterS => n.
rewrite sub0r normrN normrV ?unitfE ?gt_eqF//.
rewrite ger0_norm; last by rewrite ltW.
rewrite ltr_pinv; last 2 first.
  by rewrite inE unitfE u0 andbT gt_eqF.
  by rewrite inE unitfE ltr_paddl// andbT gt_eqF.
move/ltW; apply: le_trans.
by rewrite (le_trans (ler_norm _))// ler_addl.
Qed.

Definition isl d (R : realType) (X : measurableType d)
    (nu : {smeasure set X -> \bar R}) S l := (l != 0%N) &&
  `[< exists F, [/\ F `<=` S, measurable F & nu F >= (l%:R^-1)%:E] >].

Lemma nset_isl d (R : realType) (X : measurableType d)
    (nu : {smeasure set X -> \bar R}) S : measurable S ->
  ~ negative_set nu S -> exists n, isl nu S n.
Proof.
move=> mS=> /not_andP[/[1!inE]//|].
move=> /existsNP[F] /not_implyP[/[1!inE] mF] /not_implyP[FS].
move/negP; rewrite -ltNge => nuF0.
exists `|ceil (fine(nu F))^-1|%N; apply/andP; split.
  rewrite -lt0n absz_gt0 gt_eqF// ceil_gt0// invr_gt0// fine_gt0// nuF0/=.
  by rewrite -ge0_fin_numE ?isfinite// ltW.
apply/asboolP; exists F; split => //.
rewrite -[leRHS](@fineK _ (nu F)) ?isfinite// lee_fin.
rewrite -[leRHS](invrK (fine (nu F))) ler_pinv; last 2 first.
    rewrite inE unitfE -normr_gt0 ger0_norm// andbb.
    rewrite ltr0n absz_gt0 gt_eqF// ceil_gt0//= invr_gt0 fine_gt0// nuF0/=.
    by rewrite -ge0_fin_numE ?isfinite// ltW.
  rewrite inE unitfE andb_idl; last by move/gt_eqF/negbT.
  by rewrite invr_gt0 fine_gt0// nuF0/= -ge0_fin_numE ?isfinite// ltW.
by rewrite natr_absz ger0_norm ?ceil_ge// ceil_ge0// invr_ge0 fine_ge0// ltW.
Qed.

Lemma lt_trivIset (T: Type) (F : nat -> set T) :
  (forall n m, (m < n)%N -> F m `&` F n = set0) ->
  trivIset setT F.
Proof.
move=> h; apply/trivIsetP => m n _ _; rewrite neq_lt => /orP[|].
  exact: h.
by rewrite setIC; exact: h.
Qed.

Lemma positive_set_0 d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
  (forall N, negative_set nu N -> nu N = 0) ->
    (forall S, S \in measurable -> nu S >= 0).
Proof.
move=> nset0 S /[1!inE] mS; rewrite leNgt; apply/negP => nuS0.
suff [Fk [mFk [FkS [Fkpos [tFk [nuFk smallest]]]]]] :
  {Fk : nat -> set X * nat |
  (forall n, measurable (Fk n).1) /\
  (forall n, (Fk n).1 `<=` S) /\
  (forall n, (Fk n).2 != O) /\
  trivIset setT (fun n => (Fk n).1) /\
  (forall n, nu (Fk n).1 >= (Fk n).2%:R^-1%:E) /\
  (forall n (B : set X), measurable B -> B `<=` S `\` \bigcup_i (Fk i).1 -> nu B < (Fk n).2%:R^-1%:E) }.
pose F := \bigcup_m (Fk m).1.
have mF : measurable F by exact: bigcupT_measurable.
have FS : F `<=` S by move=> x [k _]; exact: FkS.
have nuFE : nu F = \sum_(k <oo) (nu (Fk k).1).
    apply/esym/cvg_lim => //.
    exact: (smeasure_semi_sigma_additive (fun k => (Fk k).1)).
have limk : (fun m => (Fk m).2%:R : R) --> +oo%R.
  suff : (fun m => (Fk m).2%:R^-1) --> (0 : R)%R.
    apply: inv_cvg => // n.
    by rewrite lt_neqAle eq_sym pnatr_eq0 Fkpos/= ler0n.
  apply: (@cvg_series_cvg_0 _ [normedModType R of R^o]).
  suff : \sum_(k <oo) (Fk k).2%:R^-1%:E < +oo :> \bar R.
    (* TODO: lemma *)
    move=> ?; apply: nondecreasing_is_cvg.
      move=> m n mn; rewrite /series/=.
      rewrite -(subnKC mn) {2}/index_iota subn0 iotaD big_cat/=.
      rewrite add0n -{2}(subn0 m) -/(index_iota _ _) ler_addl.
      exact: sumr_ge0.
    exists (fine (\sum_(k <oo) ((Fk k).2%:R^-1)%:E)).
    rewrite /ubound/= => _ [n _ <-]; rewrite -lee_fin fineK//; last first.
      by rewrite fin_num_abs gee0_abs//; exact: nneseries_ge0.
    by rewrite -sumEFin; exact: nneseries_lim_ge.
  rewrite (@le_lt_trans _ _ (nu F))//.
    rewrite nuFE.
    by apply: lee_nneseries => k _; [rewrite lee_fin|exact: nuFk].
  by rewrite ltey_eq isfinite.
have /nset0 nuSF0 : negative_set nu (S `\` F).
  split; first by rewrite inE; exact: measurableD.
  move=> G /[1!inE] mG GSF.
  have Gk m : nu G < (Fk m).2%:R^-1%:E.
    have /smallest : G `<=` S `\` F by [].
    exact.
    (* have /smallest : G `<=` S `\` \big[setU/set0]_(i < m) (Fk i).1.
      by apply: (subset_trans GSF); apply: setDS; exact: bigsetU_bigcup.
    by rewrite ltNge => /negP; apply.*)
  rewrite -(@fineK _ (nu G)) ?isfinite// lee_fin.
  apply/ler0_addgt0P => _/posnumP[e].
  have [m kme] : exists m, ((Fk m).2%:R^-1 <= e%:num)%R.
    move/cvgPpinfty : limk => /(_ e%:num^-1) [N _] /(_ _ (leqnn N)).
    rewrite -(@invrK _ (Fk N).2%:R) ler_pinv; last 2 first.
      by rewrite inE unitfE gt_eqF/=.
      rewrite inE unitfE invr_gt0 invr_eq0 pnatr_eq0 Fkpos/=.
      by rewrite lt_neqAle eq_sym pnatr_eq0 Fkpos ler0n.
    by move=> Ne; exists N.
  rewrite (le_trans _ kme)// -lee_fin fineK ?isfinite//.
  exact/ltW/Gk.
have : nu (S `\` F) < 0.
  rewrite s_measureD// setIidr// suber_lt0 ?isfinite//.
  rewrite (lt_le_trans nuS0)// nuFE; apply: nneseries_ge0 => k _.
  by rewrite (le_trans _ (nuFk k)).
by rewrite nuSF0 ltxx.
have NnsetS : ~ negative_set nu S by move: nuS0 => /[swap] /nset0 ->; rewrite ltxx.
pose seq_type (A : set X * nat * set X) :=
  measurable A.1.1 /\
  A.1.1 `<=` S /\
  A.1.2 != 0%N /\
  (A.1.2%:R^-1%:E <= nu A.1.1 /\
  measurable A.2 /\
  A.2 `<=` S /\
  0 <= nu A.2).
pose P (FkU1 FkU2 : {A : set X * nat * set X | seq_type A}):=
  (proj1_sig FkU2).1.1 `<=` S `\` (proj1_sig FkU1).2 /\
  (proj1_sig FkU2).2 = (proj1_sig FkU1).2 `|` (proj1_sig FkU2).1.1 /\
  (forall l B, l != 0%N -> measurable B -> B `<=` S `\` (proj1_sig FkU1).2 -> l%:R^-1%:E <= nu B -> (l >= (proj1_sig FkU2).1.2)%N).
have H0 : exists n, isl nu S n := nset_isl mS NnsetS.
pose k0 := ex_minn H0.
apply/cid.
have [k0_neq0 [F0 [F0S mF0 k0F0]]] : k0 != O /\
    exists F0, [/\ F0 `<=` S, measurable F0 & nu F0 >= (k0%:R ^-1)%:E].
  rewrite {}/k0.
  case: ex_minnP => l /andP[l0 /asboolP[F0 [F0S mF0 lF0]]] Sl.
  by split => //; exists F0.
have nuF0_ge0 : 0 <= nu F0 by rewrite (le_trans _ k0F0).
have : { FkU : nat -> {A : set X * nat * set X | seq_type A} |
    FkU 0%nat = (exist _ (F0, k0, F0)
      (conj mF0
      (conj F0S
      (conj k0_neq0
      (conj k0F0
      (conj mF0
      (conj F0S
            nuF0_ge0))))))) /\
    forall n, P (FkU n) (FkU n.+1) }.
  apply dependent_choice_Type.
  move=> [[[F k] U] [/= mF [FS [k_neq0 [kF [mU [US nuU0]]]]]]].
  have NnsetSU : ~ negative_set nu (S `\` U).
    apply: (contra_not _ _ (nset0 (S `\` _))).
    apply/eqP.
    by rewrite lt_eqF// s_measureD// setIidr// suber_lt0 ?isfinite// (lt_le_trans nuS0).
  have mSU : measurable (S `\` U) by exact: measurableD.
  have H1 : exists n, isl nu (S `\` U) n := nset_isl mSU NnsetSU.
  pose k1 := ex_minn H1.
  apply/cid.
  have [k1_neq0 [F1 [F1SU mF1 k1F1]]] : k1 != O /\
    exists F1, [/\ F1 `<=` S `\` U, measurable F1 & (k1%:R ^-1)%:E <= nu F1].
    rewrite {}/k1.
    case: ex_minnP => l /andP[l0 /asboolP[F2 [F2S mF2 lF2]]] saidai.
    by split => //; exists F2.
  have F1S : F1 `<=` S by apply: (subset_trans F1SU); exact: subDsetl.
  pose U1 := U `|` F1.
  have mU1 : measurable U1 by exact: measurableU.
  have U1S : U1 `<=` S by rewrite /U1 subUset.
  have nuU1_ge0 : 0 <= nu U1.
    rewrite s_measureU//; first by rewrite adde_ge0// (le_trans _ k1F1).
    rewrite setIC; apply/disjoints_subset.
    apply (subset_trans F1SU).
    rewrite -setTD.
    exact: setSD.
  exists (exist _ (F1, k1, U1)
      (conj mF1
      (conj F1S
      (conj k1_neq0
      (conj k1F1
      (conj mU1
      (conj U1S
            nuU1_ge0))))))) => //.
  split => //.
  split => //.
  rewrite /sval/=.
  move=> l B l0 mB BSU lB.
  rewrite /k1.
  case: ex_minnP => m /andP[m0 /asboolP[C [CSU mC mnuC]]] h.
  apply h.
  rewrite /isl l0/=.
  apply/asboolP.
  by exists B; split.
move=> [FkU [FkU0 PFkU]].
exists (fun n => (proj1_sig (FkU n)).1).
split.
  move=> n.
  rewrite /sval/=.
  by case: (FkU n) => -[Fn U] [].
split.
  move=> n.
  rewrite /sval/=.
  by case: (FkU n) => -[Fn U] [_ []].
split.
  move=> n.
  rewrite /sval/=.
  by case: (FkU n) => -[Fn U] [_ [_ []]].
have Ubig n : (proj1_sig (FkU n)).2 = \big[setU/set0]_(i < n.+1) (proj1_sig (FkU i)).1.1.
  elim: n => [|n ih]; rewrite /sval/=.
    by rewrite FkU0/= big_ord_recr/= big_ord0 set0U FkU0.
  rewrite /sval/= in ih.
  have [_ [-> _]] := PFkU n.
  by rewrite big_ord_recr/= -ih.
rewrite /sval/= in Ubig.
split.
  (*TODO: clean*)
  rewrite /P /sval/= in PFkU *.
  apply: lt_trivIset => n.
  have [m] := ubnP n; elim: m n => //= m IHm [_ []//|n] /=.
  rewrite ltnS => nm k; rewrite ltnS => kn; move: kn IHm.
  rewrite leq_eqVlt => /orP[/eqP -> IHm|kn IHm].
    rewrite setIC; apply/disjoints_subset.
    move: n nm => [m0|n nm].
      rewrite FkU0/=.
      have := PFkU O.
      rewrite FkU0/= => -[FkU1S _].
      apply: (subset_trans FkU1S).
      rewrite -setTD.
      exact: setSD.
    have [K1 _] := PFkU n.+1.
    have [_ [K2 _]] := PFkU n.
    apply (subset_trans K1).
    rewrite -setTD.
    apply: setDSS => //.
    rewrite K2.
    exact: subsetUr.
  have {}IHm := IHm _ nm _ kn.
  rewrite setIC; apply/disjoints_subset.
  have [K1 _] := PFkU n.
  have [_ [K2 _]] := PFkU n.-1.
  apply (subset_trans K1).
  rewrite -setTD.
  apply: setDSS => //.
  rewrite prednK in K2; last by rewrite (leq_trans _ kn).
  rewrite K2 Ubig prednK; last by rewrite (leq_trans _ kn).
  apply: (subset_trans _ (@subsetUl _ _ _)). (*TODO: lemma*)
  rewrite -(bigcup_mkord _ (fun i => (let (a, _) := FkU i in a).1.1)).
  exact: (@bigcup_sup _ _ _ _ (fun i => (let (a, _) := FkU i in a).1.1)).
split.
  move=> n.
  rewrite /sval/=.
  by case: (FkU n) => -[Fn U] [_ [_ [_ []]]].
rewrite /sval/=.
move=> n G mG GFS.
rewrite ltNge; apply/negP => knG.

have limk : (fun m => (proj1_sig (FkU m)).1.2%:R : R) --> +oo%R.
  suff : (fun m => (proj1_sig (FkU m)).1.2%:R^-1) --> (0 : R)%R.
    apply: inv_cvg => // n'.
    rewrite lt_neqAle eq_sym pnatr_eq0.
    rewrite /sval/=.
    have -> : (let (a, _) := FkU n' in a).1.2 != 0%N.
      by case: (FkU n') => -[[? ?] ?] [_ [_ []]].
    by rewrite ler0n.
  apply: (@cvg_series_cvg_0 _ [normedModType R of R^o]).
  suff : \sum_(k <oo) (proj1_sig (FkU k)).1.2%:R^-1%:E < +oo :> \bar R.
    (* TODO: lemma *)
    move=> ?; apply: nondecreasing_is_cvg.
      move=> m n' mn'; rewrite /series/=.
      rewrite -(subnKC mn') {2}/index_iota subn0 iotaD big_cat/=.
      rewrite add0n -{2}(subn0 m) -/(index_iota _ _) ler_addl.
      exact: sumr_ge0.
    exists (fine (\sum_(k <oo) ((proj1_sig (FkU k)).1.2%:R^-1)%:E)).
    rewrite /ubound/= => _ [n' _ <-]; rewrite -lee_fin fineK//; last first.
      by rewrite fin_num_abs gee0_abs//; exact: nneseries_ge0.
    by rewrite -sumEFin; exact: nneseries_lim_ge.
  pose F := \bigcup_m (proj1_sig (FkU m)).1.1.
  have mF : measurable F.
    apply: bigcupT_measurable.
    move=> i.
    rewrite /sval/=.
    by case: (FkU i) => -[[? ?] ?] [].
  have nuFE : nu F = \sum_(k <oo) (nu (proj1_sig (FkU k)).1.1).
    apply/esym/cvg_lim => //.
    apply: (smeasure_semi_sigma_additive (fun k => (proj1_sig (FkU k)).1.1)) => //.
    move=> i.
    rewrite /sval/=.
    by case: (FkU i) => -[[? ?] ?] [].
(* copipe *)
  rewrite /P /sval/= in PFkU *.
  apply: (@lt_trivIset _ (fun k : nat => (let (a, _) := FkU k in a).1.1)) => n'.
  have [m] := ubnP n'; elim: m n' => //= m IHm [_ []//|n'] /=.
  rewrite ltnS => n'm k; rewrite ltnS => kn'; move: kn' IHm.
  rewrite leq_eqVlt => /orP[/eqP -> IHm|kn' IHm].
    rewrite setIC; apply/disjoints_subset.
    move: n' n'm => [m0|n' n'm].
      rewrite FkU0/=.
      have := PFkU O.
      rewrite FkU0/= => -[FkU1S _].
      apply: (subset_trans FkU1S).
      rewrite -setTD.
      exact: setSD.
    have [K1 _] := PFkU n'.+1.
    have [_ [K2 _]] := PFkU n'.
    apply (subset_trans K1).
    rewrite -setTD.
    apply: setDSS => //.
    rewrite K2.
    exact: subsetUr.
  have {}IHm := IHm _ n'm _ kn'.
  rewrite setIC; apply/disjoints_subset.
  have [K1 _] := PFkU n'.
  have [_ [K2 _]] := PFkU n'.-1.
  apply (subset_trans K1).
  rewrite -setTD.
  apply: setDSS => //.
  rewrite prednK in K2; last by rewrite (leq_trans _ kn').
  rewrite K2 Ubig prednK; last by rewrite (leq_trans _ kn').
  apply: (subset_trans _ (@subsetUl _ _ _)). (*TODO: lemma*)
  rewrite -(bigcup_mkord _ (fun i => (let (a, _) := FkU i in a).1.1)).
  exact: (@bigcup_sup _ _ _ _ (fun i => (let (a, _) := FkU i in a).1.1)).
(* /copipe *)
  rewrite (@le_lt_trans _ _ (nu F))//.
    rewrite nuFE.
    apply: lee_nneseries => k _; [rewrite lee_fin|].
    by done.
    by case: (FkU k) => -[[? ?] ?] [/= _ [_ [_ [? _]]]].
  by rewrite ltey_eq isfinite.

have [m [nm Hm]] : exists m, (n < m)%N /\ ((let (a, _) := FkU n in a).1.2 < (let (a, _) := FkU m in a).1.2)%N.
  move/cvgPpinfty_lt : limk.
  move/(_ (let (a, _) := FkU n in a).1.2%:R).
  rewrite /sval/=.
  move=> [n0 _ Hn0].
  have n0n : (n0 <= n + n0.+1)%N.
    by rewrite -addSnnS leq_addl.
  have ? := (Hn0 (n + n0.+1)%N n0n).
  exists (n + n0.+1)%N; split => //.
    by rewrite -addSnnS ltn_addr//.
  rewrite -(@ltr_nat R).
  done.
have {}GFS : G `<=` S `\` \big[setU/set0]_(i < m) (let (a, _) := FkU i in a).1.1.
  apply: (subset_trans GFS).
  apply: setDS.
  exact: bigsetU_bigcup.
have [_ [_]] := PFkU m.-1.
rewrite /sval/=.
rewrite Ubig.
have kn_neq0 : (let (a, _) := FkU n in a).1.2 != 0%N.
  by case: (FkU n) => -[[? ?] ?] [_ [_ []]].
move/(_ (let (a, _) := FkU n in a).1.2 G kn_neq0 mG).
rewrite prednK//; last by rewrite (leq_trans _ nm).
move=> /(_ GFS knG).
apply/negP.
by rewrite -ltnNge.
Qed.

Theorem Hahn_decomposition d (X : measurableType d) (R : realType) (nu : {smeasure set X -> \bar R}) :
  exists P N, [/\ positive_set nu P, negative_set nu N, P `|` N = setT & P `&` N = set0].
=======
Lemma floor_ge_int (R : realType) (x : R) (z : int) : (z%:~R <= x)%R = (z <= floor x)%R.
Proof. by rewrite Rfloor_ge_int RfloorE ler_int. Qed.
Lemma ceil_le_int (R : realType) (x : R) (z : int) : (x <= z%:~R)%R = (ceil x <= z)%R.
Proof.
rewrite /ceil.
rewrite ler_oppl.
rewrite -floor_ge_int//.
rewrite -ler_oppr.
rewrite mulrNz.
rewrite opprK.
done.
Qed.

Lemma sube_lt0 (R : realDomainType) (x y : \bar R) : y \is a fin_num -> (x - y < 0) = (x < y).
Admitted.

Lemma lt_succ_floor: forall [R : realType] (x : R), (x < ((floor x)%:~R + 1))%R.
Admitted.

Proposition positive_set_0 d (R : realType) (X : measurableType d)
          (nu : {smeasure set X -> \bar R}) :
            (forall N, negative_set nu N -> (nu N = 0)%E) ->
              (forall S, (S \in measurable) -> (nu S >= 0)%E).
Proof.
(* Reductio ad absurdum *)
move=> H0 S Sm.
rewrite leNgt.
apply /negP.
move=> abs.

have not_negative_set_S: ~ negative_set nu S.
  move: abs.
  move=> /[swap].
  move /H0.
  move=> ->.
  by rewrite ltxx.
(*
have : exists F1 k1,  F1 `<=` S /\ measurable F1 /\
      (nu F1 >= (k1.+1 %:R ^-1)%:E)%E /\
        (forall (l : nat), (nu F1 >= (l%:R ^-1)%:E)%E ->
          (l >= k1.+1)%nat).
  move:not_negative_set_S.
  rewrite /negative_set.
  move=> /not_andP.
  case.
    done.
  move /existsNP.
  case.
  move=> F.
  move /not_implyP.
  case.
  move=> mF.
  move/not_implyP.
  case.
  move=> FS.
  move/negP.
  rewrite -ltNge.
  move=> F0.
  exists F.
  exists `|(floor (fine(nu F)) ^-1)|%N.
  split => //.
  split.
    by rewrite inE in mF.
  split.
    rewrite [leRHS](_ : nu F = (fine (nu F))%:E); last first.
      rewrite fineK//.
      rewrite inE in mF.
      rewrite isfinite //.
    rewrite lee_fin.
    rewrite -[leRHS](invrK (fine (nu F))).
    rewrite ler_pinv; last 2 first.
        rewrite inE unitfE -normr_gt0 ger0_norm // andbb.
        rewrite ltr0n //.
(*
        rewrite absz_gt0.
        rewrite gt_eqF//.
        rewrite ceil_gt0//=.
        rewrite invr_gt0.
        rewrite lt0R//.
        rewrite F0.
        rewrite andTb.
        rewrite -ge0_fin_numE ; last exact/ltW.
        rewrite inE in mF.
        by rewrite isfinite//.
*)
      rewrite inE unitfE.
      rewrite andb_idl ; last by move/gt_eqF/negbT.
      rewrite invr_gt0.
      rewrite lt0R//.
      rewrite F0.
      rewrite andTb.
      rewrite -ge0_fin_numE ; last exact/ltW.
      rewrite inE in mF.
      by rewrite isfinite.
    rewrite -addn1.
    rewrite natrD.
    rewrite natr_absz.
    rewrite ger0_norm; last first.
      rewrite floor_ge0 //.
      rewrite invr_ge0.
      rewrite le0R //.
      exact:ltW.
    apply/ltW.
    by rewrite lt_succ_floor.
(*
    rewrite natr_absz.
    rewrite ger0_norm; last first.
      rewrite ceil_ge0 //.
      rewrite invr_ge0.
      rewrite le0R //.
      by rewrite ltW.
    exact : ceil_ge.
*)
  move=> l lF.
  rewrite -(@ler_nat R).
  rewrite -addn1.
  rewrite natrD.
  rewrite natr_absz.
  rewrite ger0_norm; last first.
    rewrite floor_ge0 //.
    rewrite invr_ge0.
    apply/ltW.
    apply : lt0R.
    rewrite F0.
    rewrite andTb.
    rewrite -ge0_fin_numE ; last exact/ltW.
    rewrite inE in mF.
    by rewrite isfinite.

rewrite (_ : _ + _ = (floor (fine (nu F))^-1 + 1)%:~R ); last first.
  rewrite -natrD.
  rewrite addn1.
  rewrite -(absz_nat l).
  rewrite natr_absz.
  rewrite (natz 1).
  rewrite ler_int.
  rewrite -floor_le_int.
  rewrite -natr_absz.
  admit.
*)
have : exists F1 k1,  F1 `<=` S /\ measurable F1 /\ (nu F1 >= (k1%:R ^-1)%:E)%E
      /\ k1 != 0%N /\ (forall (l : nat), (nu F1 >= (l%:R ^-1)%:E)%E ->
        (l >= k1)%nat).
  move:not_negative_set_S.
  rewrite /negative_set.
  move=> /not_andP.
  case.
    done.
  move /existsNP.
  case.
  move=> F.
  move /not_implyP.
  case.
  move=> mF.
  move/not_implyP.
  case.
  move=> FS.
  move/negP.
  rewrite -ltNge.
  move=> F0.
  exists F.
  exists `|(ceil (fine(nu F)) ^-1)|%N.
  split => //.
  split.
    by rewrite inE in mF.
  split.
    rewrite [leRHS](_ : nu F = (fine (nu F))%:E); last first.
      rewrite fineK//.
      rewrite inE in mF.
      rewrite isfinite //.
    rewrite lee_fin.
    rewrite -[leRHS](invrK (fine (nu F))).
    rewrite ler_pinv; last 2 first.
        rewrite inE unitfE -normr_gt0 ger0_norm // andbb.
        rewrite ltr0n.
        rewrite absz_gt0.
        rewrite gt_eqF//.
        rewrite ceil_gt0//=.
        rewrite invr_gt0.
        rewrite lt0R//.
        rewrite F0.
        rewrite andTb.
        rewrite -ge0_fin_numE ; last exact/ltW.
        rewrite inE in mF.
        by rewrite isfinite//.
      rewrite inE unitfE.
      rewrite andb_idl ; last by move/gt_eqF/negbT.
      rewrite invr_gt0.
      rewrite lt0R//.
      rewrite F0.
      rewrite andTb.
      rewrite -ge0_fin_numE ; last exact/ltW.
      rewrite inE in mF.
      by rewrite isfinite.
    rewrite natr_absz.
    rewrite ger0_norm; last first.
      rewrite ceil_ge0 //.
      rewrite invr_ge0.
      rewrite le0R //.
      by rewrite ltW.
    exact : ceil_ge.
  split.
    rewrite -lt0n.
    rewrite absz_gt0.
    rewrite gt_eqF//.
    rewrite ceil_gt0//.
    rewrite invr_gt0//.
    apply/lt0R.
    rewrite F0 //.
    rewrite -ge0_fin_numE ; last exact/ltW.
    rewrite inE in mF.
    by rewrite isfinite.
  move=> l lF.
  rewrite -(@ler_nat R).
  rewrite natr_absz.
  rewrite ger0_norm; last first.
    rewrite /ceil.
    rewrite oppr_ge0.
    rewrite floor_le0 //.
    rewrite oppr_le0.
    rewrite invr_ge0.
    apply/ltW.
    apply : lt0R.
    rewrite F0.
    rewrite andTb.
    rewrite -ge0_fin_numE ; last exact/ltW.
    rewrite inE in mF.
    by rewrite isfinite.
  rewrite -(absz_nat l).
  rewrite natr_absz.
  rewrite ler_int.
  rewrite -ceil_le_int.
  rewrite -natr_absz.
  admit.

move=> [F1 [k1]].
move=> [F1S [mF1 [k1F1 [k1n0 minimum_k1]]]].
have not_negative_set_SF1: ~ negative_set nu (S `\` F1).
  apply: (contra_not _ _ (H0 (S `\` F1))).
  apply/eqP.
  rewrite lt_eqF//.
  rewrite s_measureD//; last first.
    by rewrite inE in Sm.
  rewrite setIidr//.
  rewrite sube_lt0.
    rewrite (lt_le_trans abs)//.
    rewrite (le_trans _ k1F1)//.
  apply isfinite.
  exact:mF1.
have F10 : (0 < nu F1)%E.
  rewrite (lt_le_trans _ k1F1)//.
  admit.

pose P (FkU1 FkU2:  {A : set X * nat * set X | measurable A.1.1 /\ A.1.1 `<=` S
                     /\ (nu A.1.1 > 0 )%E
                     /\ ((nu (A.1.1)) >= (A.1.2%:R ^-1)%:E)%E
                     /\ (A.1.2 != 0)%nat
                     /\ (forall (l : nat),
                          (nu (A.1.1) >= (l%:R ^-1)%:E)%E
                             -> (l >= A.1.2)%nat )
                     /\ measurable A.2 /\ A.2 `<=` S /\ 0 < nu A.2} ):=
       (proj1_sig FkU2).1.1
       `<=` S `\` (proj1_sig FkU1).2
          (*/\ ((proj1_sig FkU1).1.2 <= (proj1_sig FkU2).1.2)%nat*)
          /\ ((proj1_sig FkU2).2) = (proj1_sig FkU1).2 `|` (proj1_sig FkU2).1.1.
have : { FkU : nat -> {A : set X * nat * set X | measurable A.1.1
                     /\ A.1.1 `<=` S
                     /\ (nu A.1.1 > 0 )%E
                     /\ ((nu (A.1.1)) >= (A.1.2%:R ^-1)%:E)%E
                     /\ (A.1.2 != 0)%nat
                     /\ (forall (l : nat),
                          (nu (A.1.1) >= (l%:R ^-1)%:E)%E
                             -> (l >= A.1.2)%nat )
                     /\ measurable A.2 /\ A.2 `<=` S /\ 0 < nu A.2} |
           FkU 0%nat =
             (((exist _ (F1, k1, F1) (conj mF1
                                     (conj F1S
                                     (conj F10
                                     (conj k1F1
                                     (conj k1n0
                                     (conj minimum_k1
                                     (conj mF1
                                     (conj F1S
                                           F10 ))))))))
                                                 )))
                /\ forall n, P (FkU n) (FkU n.+1) }.
  apply dependent_choice_Type.
  move=> [[[F k] U] [mF [FS [F0 [Fk [kn0 [mink [mU [US U0]]]]]]]]].
  have : exists F' k',  F' `<=` S `\` U
                        /\ measurable F'
                        /\ (nu F' >= (k'%:R ^-1)%:E)%E
                        /\ k' != 0%N
                        /\ (forall (l : nat),
         (nu F' >= (l%:R ^-1)%:E)%E -> (l >= k')%nat).
    have not_negative_set_SU : ~ negative_set nu (S `\` U).
      apply: (contra_not _ _ (H0 (S `\` _))).
      apply/eqP.
      rewrite lt_eqF//.
      rewrite s_measureD//; last first.
        rewrite inE in Sm =>//.
      rewrite setIidr//.
      rewrite sube_lt0.
        rewrite (lt_le_trans abs)//.
        by rewrite ltW.
        apply : isfinite.
      exact mU.
    move:not_negative_set_SU.
    rewrite /negative_set.
    move=> /not_andP.
    case.
      apply : absurd.
      rewrite inE; apply : measurableD => //.
      by rewrite inE in Sm.
    move /existsNP.
    case.
    move=> F2.
    move /not_implyP.
    case.
    move=> mF2.
    move/not_implyP.
    case.
    move=> F2SU.
    move/negP.
    rewrite -ltNge.
    move=> F20.
    exists F2.
    exists `|(ceil (fine(nu F2)) ^-1)|%N.
    split => //.
    split.
      by rewrite inE in mF2.
    split.
      rewrite [leRHS](_ : nu F2 = (fine (nu F2))%:E); last first.
        rewrite fineK//.
        rewrite inE in mF2.
        rewrite isfinite //.
      rewrite lee_fin.
      rewrite -[leRHS](invrK (fine (nu F2))).
      rewrite ler_pinv; last 2 first.
          rewrite inE unitfE -normr_gt0 ger0_norm // andbb.
          rewrite ltr0n.
          rewrite absz_gt0.
          rewrite gt_eqF//.
          rewrite ceil_gt0//=.
          rewrite invr_gt0.
          rewrite lt0R//.
          rewrite F20.
          rewrite andTb.
          rewrite -ge0_fin_numE ; last exact/ltW.
          rewrite inE in mF2.
          by rewrite isfinite//.
        rewrite inE unitfE.
        rewrite andb_idl ; last by move/gt_eqF/negbT.
        rewrite invr_gt0.
        rewrite lt0R//.
        rewrite F20.
        rewrite andTb.
        rewrite -ge0_fin_numE ; last exact/ltW.
        rewrite inE in mF2.
        by rewrite isfinite.
      rewrite natr_absz.
      rewrite ger0_norm; last first.
        rewrite ceil_ge0 //.
        rewrite invr_ge0.
        rewrite le0R //.
        by rewrite ltW.
      exact : ceil_ge.
    split.
      rewrite -lt0n.
      rewrite absz_gt0.
      rewrite gt_eqF//.
      rewrite ceil_gt0//.
      rewrite invr_gt0//.
      apply/lt0R.
      rewrite F20 //.
      rewrite -ge0_fin_numE ; last exact/ltW.
      rewrite inE in mF2.
      by rewrite isfinite.
    move=> l lF.
    rewrite -(@ler_nat R).
    rewrite natr_absz.
    rewrite ger0_norm; last first.
      rewrite /ceil.
      rewrite oppr_ge0.
      rewrite floor_le0 //.
      rewrite oppr_le0.
      rewrite invr_ge0.
      apply/ltW.
      apply : lt0R.
      rewrite F20.
      rewrite andTb.
      rewrite -ge0_fin_numE ; last exact/ltW.
      rewrite inE in mF2.
      by rewrite isfinite.
    rewrite -(absz_nat l).
    rewrite natr_absz.
    rewrite ler_int.
    rewrite -ceil_le_int.
    rewrite -natr_absz.
    admit.
  move/cid=> [F'].
  move/cid=> [k'].
  move=> [F'SU [mF' [k'F' [k'n0 minimum_k']]]].
  have F'S : F' `<=` S.
    apply (subset_trans F'SU).
    exact : subDsetl.
  have F'0 : (nu F' > 0)%E.
    apply : (lt_le_trans _ k'F').
    rewrite lte_fin.
    rewrite invr_gt0.
    rewrite ltr0n.
    by rewrite lt0n.
  have mUF' : measurable (U `|` F').
    exact :measurableU.
  have UF'S : U `|` F' `<=` S.
    by rewrite subUset.
  have UF'0 : (nu (U `|` F') > 0)%E.
    rewrite s_measureU //.
      rewrite adde_gt0 //.
    rewrite setIC.
    apply/disjoints_subset.
    apply (subset_trans F'SU).
    rewrite -setTD.
    by apply : setSD.

  exists ((exist _ (F', k', U `|` F') (conj mF'
                                      (conj F'S
                                      (conj F'0
                                      (conj k'F'
                                      (conj k'n0
                                      (conj minimum_k'
                                      (conj mUF'
                                      (conj UF'S
                                            UF'0 ))))))))
           )).
  rewrite /P /=.
  split => //.
(*  apply mink => //=.
  apply : (le_trans k'F').
  rewrite leNgt.
  apply /negP.
  have : (k <= k')%N.*)
case.
move=> /= FkU.
case.
move=> FkU0.
move=> Hn.
pose F := \bigcup_n (proj1_sig (FkU n)).1.1.
have /H0 : negative_set nu (S `\` F).
  rewrite /negative_set.
  split.
    admit.
  move=> G mG GSF.
  have : forall n, (nu G < (proj1_sig (FkU n)).1.2%:R^-1%:E)%E.
    have : forall n, (G `<=` S `\` (proj1_sig (FkU n)).2).
      admit.
    move=> GS n.
    rewrite //=.
  admit.
have : (nu (S `\` F) < 0).
      rewrite s_measureD //.
      have FS : F `<=` S.
        admit.
      rewrite setIidr =>//.
      rewrite sube_lt0.
        admit.
      admit.
    by rewrite inE in Sm.
  admit.
move=> /[swap].
move=> ->.
by rewrite ltxx.
Admitted.


Theorem Hahn_decomposition d (R : realType) (X : measurableType d) (nu : {smeasure set X -> \bar R}) :
     exists P N, [/\ (positive_set nu P), (negative_set nu N), (P `|` N = setT) & (P `&` N = set0)].
>>>>>>> abs_cont_measure
Proof.
Admitted.

(* Definition  : measureable -> R :=  *)

<<<<<<< abs_cont_measure
Require Import lebesgue_integral.

Theorem Radon_Nikodym_finite_nonnegative d (X : measurableType d) (R : realType)
    (mu nu : {measure set X -> \bar R}) (mufinite : (mu setT < +oo)%E) (nufinite : (nu setT < +oo)%E) :
   nu `<< mu -> exists f : X -> \bar R, [/\
        forall x, f x >= 0,
        integrable mu setT f &
        forall E, E \in measurable -> nu E = integral mu E f].
Proof.
(*
 * Define the measurable subsets of X to be those subsets that belong to the
 *  σ-algebra measurable on which the measures mu and nu are defined.
 *)
move=> mudomnu.
pose G := [set g : X -> \bar R | [/\
  forall x, (g x >= 0)%E,
  integrable mu setT g &
  forall E, E \in measurable -> (\int[mu]_(x in E) g x <= nu E)%E] ].
(* maybe define G : set R insted of set \bar R
pose G' := [set g : X -> \bar R |
            [/\ (forall x, (g x >= 0)%E),
               integrable mu setT g &
                 forall E, E \in measurable -> fine (\int[mu]_(x in E) g x) <= fine (nu E) ] ].
*)
have neG : G !=set0.
  exists (cst 0%E); split; first by [].
  - exact: integrable0.
  - by move=> E _; by rewrite integral0.
pose IG := [set \int[mu]_x g x | g in G]%E.
have neIG : IG !=set0.
  case: neG => g [g0 g1 g2].
  by exists (\int[mu]_x g x)%E, g.
have IGbound : exists M, forall x, x \in IG -> (x <= M%:E)%E.
  exists (fine (nu setT)) => x.
  rewrite inE => -[g [g0 g1 g2] <-{x}].
  rewrite fineK; last by rewrite ge0_fin_numE.
  by rewrite (le_trans (g2 setT _))// inE.
pose M := ereal_sup IG.
have H1 : exists f : X -> \bar R, \int[mu]_x f x = M /\
                           forall E, E \in measurable -> (\int[mu]_(x in E) f x)%E = nu E.
  admit.
have [g H2] : exists g : (X -> \bar R)^nat, forall m, g m \in G /\ \int[mu]_x (g m x) >= M - m.+1%:R^-1%:E.
  (* ub_ereal_sup_adherent *)
  admit.
pose F (m : nat) (x : X) := \big[maxe/0%:E]_(j < m) (g j x).
(* have : forall m x, F m x >= 0
=======

Theorem Radon_Nikodym_finite_nonnegative d (R : realType) (X : measurableType d) (mu nu: {measure set X -> \bar R}) (mufinite : (mu setT < +oo)%E) (nufinite : (nu setT < +oo)%E):
     nu `<< mu -> exists (f : X -> \bar R), [/\(forall x, (f x >= 0)%E),
        integrable mu setT f & forall E, E \in measurable -> nu E = integral mu E f].
Proof.
(*
 * Define the measurable subsets of X to be those subsets that belong to the σ-algebra measurable on which the measures mu and nu are defined.
 * 
 *)
move=> mudomnu.
pose G := [set g : X -> \bar R |
            [/\ (forall x, (g x >= 0)%E),
               integrable mu setT g & 
                 forall E, E \in measurable -> (\int[mu]_(x in E) g x <= nu E)%E] ].
(* maybe define G : set R insted of set \bar R 
pose G' := [set g : X -> \bar R |
            [/\ (forall x, (g x >= 0)%E),
               integrable mu setT g & 
                 forall E, E \in measurable -> fine (\int[mu]_(x in E) g x) <= fine (nu E) ] ].
*) 
have neG : G !=set0.
  exists (cst 0%E).
  red.
  rewrite /=.
  rewrite /G /=.
  split => //.
    admit.
  move=> E _.
  by rewrite integral0.
pose IG := [set (\int[mu]_x g x) | g in G]%E.
have neIG : IG !=set0.
  case: neG.  
  move=> g.
  case=> g0 g1 g2.
  exists (\int[mu]_x g x)%E.
  by exists g.
have IGbound : exists (M : R), forall x, x \in IG -> (x <= M%:E)%E.
  exists (fine (nu setT)).
  move=> x.
  rewrite inE.
  case.
  move=> g.
  move=> [g0 g1 g2].
  move=> <- {x}.
  rewrite fineK.
    apply: le_trans (g2 setT _) => //.
    by rewrite inE.
  by rewrite ge0_fin_numE.
pose M := ereal_sup IG.

have H1: exists f : X -> \bar R, (\int[mu]_x f x = M)%E /\ forall E, E \in measurable -> (\int[mu]_(x in E) f x)%E = nu E.
  admit.
have : exists (g : (X -> \bar R)^nat ), forall m, g m \in G /\ (\int[mu]_x (g m x) >= M - m.+1%:R^-1%:E )%E.
  (* ub_ereal_sup_adherent *)
admit.
move=> [g H2].
pose F (m : nat) (x : X) := \big[maxe/0%:E]_(j < m) (g j x).
(* have : forall m x, F m x >= 0 
>>>>>>> abs_cont_measure
 *   forall x, 0 <= g m x, g m in G
 *)
 (* max_g2' : (T -> R)^nat :=
  fun k t => (\big[maxr/0]_(i < k) (g2' i k) t)%R. *)
<<<<<<< abs_cont_measure
pose E m j := [set x | F m x = g j x /\ forall k, (k < j)%nat -> F m x > g k x ].
=======
pose E m j := [set x | F m x = g j x /\ (forall k, (k < j)%nat -> (F m x > g k x)%E ) ].
>>>>>>> abs_cont_measure
have measurable_E m j : E m j \in measurable.
  admit.
have partition_E m : partition setT (E m) setT.
  admit.
(* Local Open Scope ereal_scope. *)
<<<<<<< abs_cont_measure
have Fleqnu m E0 (mE : E0 \in measurable) : \int[mu]_(x in E0) F m x <= nu E0.
  have H'1 : \int[mu]_(x in E0) F m x = \sum_(j < m) \int[mu]_(x in (E0 `&` (E m j))) F m x.
    admit.
  have H'2 : \sum_(j < m) (\int[mu]_(x in (E0 `&` (E m j))) F m x) =
             \sum_(j < m) (\int[mu]_(x in (E0 `&` (E m j))) g m x).
    admit.
  have H'3 : \sum_(j < m) (\int[mu]_(x in (E0 `&` (E m j))) g m x) <=
             \sum_(j < m) nu (E0 `&` (E m j)).
    admit.
  have H'4 : \sum_(j < m) (nu (E0 `&` (E m j))) = nu E0.
    admit.
  by rewrite H'1 H'2 -H'4; exact H'3.
have FminG m : F m \in G.
  admit.
have Fgeqg m : forall x, F m x >= g m x.
  admit.
have nd_F m x : nondecreasing_seq (F ^~ x).
  admit.
pose limF := fun (x : X) => lim (F^~ x).
exists limF.
have limFleqnu : forall E, \int[mu]_(x in E) limF x <= nu E.
  admit.
have limFXeqM : \int[mu]_x limF x = M.
  admit.
split.
- admit.
- admit.
- (* Reductio ad absurdum *)
  move=> E0 mE0.
  apply/eqP; rewrite eq_le limFleqnu andbT; apply/negP => abs.
  have [eps] : exists eps : {posnum R}, \int[mu]_(x in E0) (limF x + eps%:num%:E) < nu E0.
    admit.
  have sigma : {smeasure set X -> \bar R}.
    admit.
  have sigmaE : forall F, sigma F = nu F - \int[mu]_(x in F) (limF x + eps%:num%:E).
    admit.
  move : (Hahn_decomposition sigma) => [P [N [posP negN PNX PN0]]].
Admitted.

Theorem Radon_Nikodym d (X : measurableType d) (R : realType)
    (mu : {measure set X -> \bar R}) (nu : {smeasure set X -> \bar R})
    (musigmafinite : sigma_finite setT mu) :
  nu `<< mu -> exists f : X -> \bar R,
  integrable mu setT f /\ forall E, E \in measurable -> nu E = integral mu E f.
=======
have Fleqnu m E0 (mE : E0 \in measurable) : (\int[mu]_(x in E0) F m x <= nu E0)%E.  
  have H'1 : (\int[mu]_(x in E0) F m x)%E = \big[adde/0%:E]_(j < m) (\int[mu]_(x in (E0 `&` (E m j))) F m x)%E. 
    admit.
  have H'2 : (\sum_(j < m) \int[mu]_(x in (E0 `&` (E m j))) F m x)%E =
           (\sum_(j < m) (\int[mu]_(x in (E0 `&` (E m j))) g m x))%E.
    admit.
  have H'3 : (\sum_(j < m) (\int[mu]_(x in (E0 `&` (E m j))) g m x) <=
            \sum_(j < m) (nu (E0 `&` (E m j))))%E.
    admit.
  have H'4: (\sum_(j < m) (nu (E0 `&` (E m j))))%E = nu E0.
    admit.
  rewrite H'1 H'2.
  rewrite -H'4.
  exact H'3.
have FminG m : F m \in G.
  admit.
have Fgeqg m : forall x, (F m x >= g m x)%E.
  admit.
have nd_F m x : nondecreasing_seq (F^~ x). 
  admit.
pose limF := fun (x : X) => lim (F^~ x).
exists limF.
have limFleqnu : forall E, (\int[mu]_(x in E) limF x <= nu E)%E.
  admit.
have limFXeqM : (\int[mu]_x limF x = M)%E.
  admit.
split.
    admit.
  admit.
(* Reductio ad absurdum *)
move=> E0 mE0.
apply /eqP.
rewrite eq_le.
rewrite limFleqnu.
rewrite andbT.
rewrite leNgt.
apply /negP.
move=> absurd.
have : exists eps : {posnum R}, (\int[mu]_(x in E0) (limF x + eps%:num%:E) < nu E0)%E.
  admit.
move=> [eps].
have sigma : {smeasure set X -> \bar R}.
  admit.
have sigmaE : forall F, sigma F = (nu F - \int[mu]_(x in F) (limF x + eps%:num%:E))%E.
  admit.
move : (Hahn_decomposition sigma). 
move=> [P [N]].
case.
move=> posP negN PNX PN0.
Admitted.

Theorem Radon_Nikodym d (R : realType) (X : measurableType d) (mu: {measure set X -> \bar R}) (nu: {smeasure set X -> \bar R}) (musigmafinite : sigma_finite setT mu):
     nu `<< mu -> exists (f : X -> \bar R),
        integrable mu setT f /\ forall E, E \in measurable -> nu E = integral mu E f.
>>>>>>> abs_cont_measure
Proof.
Abort.

Theorem FTC2 (R : realType) (f : R -> R) (a b : R)
     (f_abscont : abs_continuous_function f (a, b) ) 
       : exists f' : R -> \bar R, summable `[a, b] f' /\
         {ae (lebesgue_measure R), forall x, x \in `[a, b] ->f' x \is a fin_num}
           /\ forall x, x \in `[a, b] -> 
             (f x - f a)%:E = (integral (lebesgue_measure R) `[a ,x] f').
Proof.
Abort.




xxx

Section lebesgue_measure.
Variable R : realType.
Let gitvs := g_measurableType (@ocitv R).

Lemma lebesgue_measure_unique (mu : {measure set gitvs -> \bar R}) :
  (forall X, ocitv X -> hlength X = mu X) ->
  forall X, measurable X -> lebesgue_measure X = mu X.
Proof.
move=> muE X mX; apply: Hahn_ext_unique => //=.
- exact: hlength_sigma_sub_additive.
- exact: hlength_sigma_finite.
Qed.


End lebesgue_measure.

Section ps_infty.
Context {T : Type}.
Local Open Scope ereal_scope.

Inductive ps_infty : set \bar T -> Prop :=
| ps_infty0 : ps_infty set0
| ps_ninfty : ps_infty [set -oo]
| ps_pinfty : ps_infty [set +oo]
| ps_inftys : ps_infty [set -oo; +oo].

Lemma ps_inftyP (A : set \bar T) : ps_infty A <-> A `<=` [set -oo; +oo].
Proof.
split => [[]//|Aoo].
by have [] := subset_set2 Aoo; move=> ->; constructor.
Qed.

Lemma setCU_Efin (A : set T) (B : set \bar T) : ps_infty B ->
                                                ~` (EFin @` A) `&` ~` B = (EFin @` ~` A) `|` ([set -oo%E; +oo%E] `&` ~` B).
Proof.
move=> ps_inftyB.
have -> : ~` (EFin @` A) = EFin @` (~` A) `|` [set -oo; +oo]%E.
  by rewrite EFin_setC setDKU // => x [|] -> -[].
rewrite setIUl; congr (_ `|` _); rewrite predeqE => -[x| |]; split; try by case.
by move=> [] x' Ax' [] <-{x}; split; [exists x'|case: ps_inftyB => // -[]].
Qed.

End ps_infty.

Section salgebra_ereal.
Variables (R : realType) (G : set (set R)).
Let measurableTypeR := g_measurableType G.
Let measurableR : set (set R) := @measurable measurableTypeR.

Definition emeasurable : set (set \bar R) :=
  [set EFin @` A `|` B | A in measurableR & B in ps_infty].

Lemma emeasurable0 : emeasurable set0.
Proof.
exists set0; first exact: measurable0.
by exists set0; rewrite ?setU0// ?image_set0//; constructor.
Qed.

Lemma emeasurableC (X : set \bar R) : emeasurable X -> emeasurable (~` X).
Proof.
move => -[A mA] [B PooB <-]; rewrite setCU setCU_Efin //.
exists (~` A); [exact: measurableC | exists ([set -oo%E; +oo%E] `&` ~` B) => //].
case: PooB.
- by rewrite setC0 setIT; constructor.
- rewrite setIUl setICr set0U -setDE.
  have [_ ->] := @setDidPl (\bar R) [set +oo%E] [set -oo%E]; first by constructor.
  by rewrite predeqE => x; split => // -[->].
- rewrite setIUl setICr setU0 -setDE.
  have [_ ->] := @setDidPl (\bar R) [set -oo%E] [set +oo%E]; first by constructor.
  by rewrite predeqE => x; split => // -[->].
- by rewrite setICr; constructor.
Qed.

Lemma bigcupT_emeasurable (F : (set \bar R)^nat) :
  (forall i, emeasurable (F i)) -> emeasurable (\bigcup_i (F i)).
Proof.
move=> mF; pose P := fun i j => measurableR j.1 /\ ps_infty j.2 /\
                            F i = [set x%:E | x in j.1] `|` j.2.
have [f fi] : {f : nat -> (set R) * (set \bar R) & forall i, P i (f i) }.
  by apply: choice => i; have [x mx [y PSoo'y] xy] := mF i; exists (x, y).
exists (\bigcup_i (f i).1).
  by apply: bigcupT_measurable => i; exact: (fi i).1.
exists (\bigcup_i (f i).2).
  apply/ps_inftyP => x [n _] fn2x.
  have /ps_inftyP : ps_infty(f n).2 by have [_ []] := fi n.
  exact.
rewrite [RHS](@eq_bigcupr _ _ _ _
    (fun i => [set x%:E | x in (f i).1] `|` (f i).2)); last first.
  by move=> i; have [_ []] := fi i.
rewrite bigcupU; congr (_ `|` _).
rewrite predeqE => i /=; split=> [[r [n _ fn1r <-{i}]]|[n _ [r fn1r <-{i}]]];
 by [exists n => //; exists r | exists r => //; exists n].
Qed.

Definition ereal_isMeasurable : isMeasurable (\bar R) :=
  isMeasurable.Build _ (Pointed.class _)
    emeasurable0 emeasurableC bigcupT_emeasurable.

End salgebra_ereal.

Section puncture_ereal_itv.
Variable R : realDomainType.
Implicit Types (y : R) (b : bool).
Local Open Scope ereal_scope.

Lemma punct_eitv_bnd_pinfty b y : [set` Interval (BSide b y%:E) +oo%O] =
  EFin @` [set` Interval (BSide b y) +oo%O] `|` [set +oo].
Proof.
rewrite predeqE => x; split; rewrite /= in_itv andbT.
- move: x => [x| |] yxb; [|by right|by case: b yxb].
  by left; exists x => //; rewrite in_itv /= andbT; case: b yxb.
- move=> [[r]|->].
  + by rewrite in_itv /= andbT => yxb <-; case: b yxb.
  + by case: b => /=; rewrite ?(ltey, leey).
Qed.

Lemma punct_eitv_ninfty_bnd b y : [set` Interval -oo%O (BSide b y%:E)] =
  [set -oo%E] `|` EFin @` [set x | x \in Interval -oo%O (BSide b y)].
Proof.
rewrite predeqE => x; split; rewrite /= in_itv.
- move: x => [x| |] yxb; [|by case: b yxb|by left].
  by right; exists x => //; rewrite in_itv /= andbT; case: b yxb.
- move=> [->|[r]].
  + by case: b => /=; rewrite ?(ltNye, leNye).
  + by rewrite in_itv /= => yxb <-; case: b yxb.
Qed.

Lemma punct_eitv_setTR : range (@EFin R) `|` [set +oo] = [set~ -oo].
Proof.
rewrite eqEsubset; split => [a [[a' _ <-]|->]|] //.
by move=> [x| |] //= _; [left; exists x|right].
Qed.

Lemma punct_eitv_setTL : range (@EFin R) `|` [set -oo] = [set~ +oo].
Proof.
rewrite eqEsubset; split => [a [[a' _ <-]|->]|] //.
by move=> [x| |] //= _; [left; exists x|right].
Qed.

End puncture_ereal_itv.

Lemma set1_bigcap_oc (R : realType) (r : R) :
   [set r] = \bigcap_i `]r - i.+1%:R^-1, r]%classic.
Proof.
apply/seteqP; split=> [x ->|].
  by move=> i _/=; rewrite in_itv/= lexx ltr_subl_addr ltr_addl invr_gt0 ltr0n.
move=> x rx; apply/esym/eqP; rewrite eq_le (itvP (rx 0%N _))// andbT.
apply/ler_addgt0Pl => e e_gt0; rewrite -ler_subl_addl ltW//.
have := rx `|floor e^-1%R|%N I; rewrite /= in_itv => /andP[/le_lt_trans->]//.
rewrite ler_add2l ler_opp2 -lef_pinv ?invrK//; last by rewrite qualifE invr_gt0.
rewrite -addn1 natrD natr_absz ger0_norm ?floor_ge0 ?invr_ge0 1?ltW//.
by rewrite -RfloorE lt_succ_Rfloor.
Qed.

Section salgebra_R_ssets.
Variable R : realType.

Definition measurableTypeR :=
  g_measurableType (@measurable (@itvs_semiRingOfSets R)).

Definition measurableR : set (set R) := @measurable measurableTypeR.

HB.instance Definition R_isMeasurable : isMeasurable R :=
  isMeasurable.Build measurableTypeR (Pointed.class R)
    measurable0 (@measurableC _) (@bigcupT_measurable _).
(*HB.instance (Real.sort R) R_isMeasurable.*)

Lemma measurable_set1 (r : R) : measurable [set r].
Proof.
rewrite set1_bigcap_oc; apply: bigcap_measurable => k // _.
by apply: sub_sigma_algebra; exact/is_ocitv.
Qed.
#[local] Hint Resolve measurable_set1 : core.

Lemma measurable_itv (i : interval R) : measurable [set` i].
Proof.
have moc (a b : R) : measurable `]a, b]%classic.
  by apply: sub_sigma_algebra; apply: is_ocitv.
have pooE (x : R) : `]x, +oo[%classic = \bigcup_i `]x, x + i%:R]%classic.
  apply/seteqP; split=> y; rewrite /= !in_itv/= andbT; last first.
    by move=> [k _ /=] /itvP->.
  move=> xy; exists `|ceil (y - x)|%N => //=.
  rewrite in_itv/= xy/= -ler_subl_addl !natr_absz/=.
  rewrite ger0_norm ?ceil_ge0 ?subr_ge0//; last exact: ltW.
  by rewrite -RceilE Rceil_ge.
have mopoo (x : R) : measurable `]x, +oo[%classic.
  by rewrite pooE; exact: bigcup_measurable.
have mnooc (x : R) : measurable `]-oo, x]%classic.
  by rewrite -setCitvr; exact/measurableC.
have ooE (a b : R) : `]a, b[%classic = `]a, b]%classic `\ b.
  case: (boolP (a < b)) => ab; last by rewrite !set_itv_ge ?set0D.
  by rewrite -setUitv1// setUDK// => x [->]; rewrite /= in_itv/= ltxx andbF.
have moo (a b : R) : measurable `]a, b[%classic.
  by rewrite ooE; exact: measurableD.
have mcc (a b : R) : measurable `[a, b]%classic.
  case: (boolP (a <= b)) => ab; last by rewrite set_itv_ge.
  by rewrite -setU1itv//; apply/measurableU.
have mco (a b : R) : measurable `[a, b[%classic.
  case: (boolP (a < b)) => ab; last by rewrite set_itv_ge.
  by rewrite -setU1itv//; apply/measurableU.
have oooE (b : R) : `]-oo, b[%classic = `]-oo, b]%classic `\ b.
  by rewrite -setUitv1// setUDK// => x [->]; rewrite /= in_itv/= ltxx.
case: i => [[[] a|[]] [[] b|[]]] => //; do ?by rewrite set_itv_ge.
- by rewrite -setU1itv//; exact/measurableU.
- by rewrite oooE; exact/measurableD.
- by rewrite set_itv_infty_infty.
Qed.

HB.instance Definition _ :=
  ereal_isMeasurable (@measurable (@itvs_semiRingOfSets R)).
(* NB: Until we dropped support for Coq 8.12, we were using
HB.instance (\bar (Real.sort R))
  (ereal_isMeasurable (@measurable (@itvs_semiRingOfSets R))).
This was producing a warning but the alternative was failing with Coq 8.12 with
  the following message (according to the CI):
  # [redundant-canonical-projection,typechecker]
  # forall (T : measurableType) (f : T -> R), measurable_fun setT f
  #      : Prop
  # File "./theories/lebesgue_measure.v", line 4508, characters 0-88:
  # Error: Anomaly "Uncaught exception Failure("sep_last")."
  # Please report at http://coq.inria.fr/bugs/.
*)

Lemma measurable_EFin (A : set R) : measurableR A -> measurable (EFin @` A).
Proof.
by move=> mA; exists A => //; exists set0; [constructor|rewrite setU0].
Qed.

Lemma emeasurable_set1 (x : \bar R) : measurable [set x].
Proof.
case: x => [r| |].
- by rewrite -image_set1; apply: measurable_EFin; apply: measurable_set1.
- exists set0 => //; [exists [set +oo%E]; [by constructor|]].
  by rewrite image_set0 set0U.
- exists set0 => //; [exists [set -oo%E]; [by constructor|]].
  by rewrite image_set0 set0U.
Qed.
#[local] Hint Resolve emeasurable_set1 : core.

Lemma itv_cpinfty_pinfty : `[+oo%E, +oo[%classic = [set +oo%E] :> set (\bar R).
Proof.
rewrite set_itvE predeqE => t; split => /= [|<-//].
by rewrite lee_pinfty_eq => /eqP.
Qed.

Lemma itv_opinfty_pinfty : `]+oo%E, +oo[%classic = set0 :> set (\bar R).
Proof.
by rewrite set_itvE predeqE => t; split => //=; apply/negP; rewrite -leNgt leey.
Qed.

Lemma itv_cninfty_pinfty : `[-oo%E, +oo[%classic = setT :> set (\bar R).
Proof. by rewrite set_itvE predeqE => t; split => //= _; rewrite leNye. Qed.

Lemma itv_oninfty_pinfty :
  `]-oo%E, +oo[%classic = ~` [set -oo]%E :> set (\bar R).
Proof.
rewrite set_itvE predeqE => x; split => /=.
- by move: x => [x| |]; rewrite ?ltxx.
- by move: x => [x h|//|/(_ erefl)]; rewrite ?ltNye.
Qed.

Lemma emeasurable_itv_bnd_pinfty b (y : \bar R) :
  measurable [set` Interval (BSide b y) +oo%O].
Proof.
move: y => [y| |].
- exists [set` Interval (BSide b y) +oo%O]; first exact: measurable_itv.
  by exists [set +oo%E]; [constructor|rewrite -punct_eitv_bnd_pinfty].
- by case: b; rewrite ?itv_opinfty_pinfty ?itv_cpinfty_pinfty.
- case: b; first by rewrite itv_cninfty_pinfty.
  by rewrite itv_oninfty_pinfty; exact/measurableC.
Qed.

Lemma emeasurable_itv_ninfty_bnd b (y : \bar R) :
  measurable [set` Interval -oo%O (BSide b y)].
Proof.
by rewrite -setCitvr; exact/measurableC/emeasurable_itv_bnd_pinfty.
Qed.

Definition elebesgue_measure' : set \bar R -> \bar R :=
  fun S => lebesgue_measure (fine @` (S `\` [set -oo; +oo]%E)).

Lemma elebesgue_measure'0 : elebesgue_measure' set0 = 0%E.
Proof. by rewrite /elebesgue_measure' set0D image_set0 measure0. Qed.

Lemma measurable_fine (X : set \bar R) : measurable X ->
  measurable [set fine x | x in X `\` [set -oo; +oo]%E].
Proof.
case => Y mY [X' [ | <-{X} | <-{X} | <-{X} ]].
- rewrite setU0 => <-{X}.
  rewrite [X in measurable X](_ : _ = Y) // predeqE => r; split.
    by move=> [x [[x' Yx' <-{x}/= _ <-//]]].
  by move=> Yr; exists r%:E; split => [|[]//]; exists r.
- rewrite [X in measurable X](_ : _ = Y) // predeqE => r; split.
    move=> [x [[[x' Yx' <- _ <-//]|]]].
    by move=> <-; rewrite not_orP => -[]/(_ erefl).
  by move=> Yr; exists r%:E => //; split => [|[]//]; left; exists r.
- rewrite [X in measurable X](_ : _ = Y) // predeqE => r; split.
    move=> [x [[[x' Yx' <-{x} _ <-//]|]]].
    by move=> ->; rewrite not_orP => -[_]/(_ erefl).
  by move=> Yr; exists r%:E => //; split => [|[]//]; left; exists r.
- rewrite [X in measurable X](_ : _ = Y) // predeqE => r; split.
    by rewrite setDUl setDv setU0 => -[_ [[x' Yx' <-]] _ <-].
  by move=> Yr; exists r%:E => //; split => [|[]//]; left; exists r.
Qed.

Lemma elebesgue_measure'_ge0 X : (0 <= elebesgue_measure' X)%E.
Proof. exact/measure_ge0. Qed.

Lemma semi_sigma_additive_elebesgue_measure' :
  semi_sigma_additive elebesgue_measure'.
Proof.
move=> /= F mF tF mUF; rewrite /elebesgue_measure'.
rewrite [X in lebesgue_measure X](_ : _ =
    \bigcup_n (fine @` (F n `\` [set -oo; +oo]%E))); last first.
  rewrite predeqE => r; split.
    by move=> [x [[n _ Fnx xoo <-]]]; exists n => //; exists x.
  by move=> [n _ [x [Fnx xoo <-{r}]]]; exists x => //; split => //; exists n.
apply: (@measure_semi_sigma_additive _ _ (@lebesgue_measure R)
  (fun n => fine @` (F n `\` [set -oo; +oo]%E))).
- move=> n; have := mF n.
  move=> [X mX [X' mX']] XX'Fn.
  apply: measurable_fine.
  rewrite -XX'Fn.
  apply: measurableU; first exact: measurable_EFin.
  by case: mX' => //; exact: measurableU.
- move=> i j _ _ [x [[a [Fia aoo ax] [b [Fjb boo] bx]]]].
  move: tF => /(_ i j Logic.I Logic.I); apply.
  suff ab : a = b by exists a; split => //; rewrite ab.
  move: a b {Fia Fjb} aoo boo ax bx.
  move=> [a| |] [b| |] /=.
  + by move=> _ _ -> ->.
  + by move=> _; rewrite not_orP => -[_]/(_ erefl).
  + by move=> _; rewrite not_orP => -[]/(_ erefl).
  + by rewrite not_orP => -[_]/(_ erefl).
  + by rewrite not_orP => -[_]/(_ erefl).
  + by rewrite not_orP => -[_]/(_ erefl).
  + by rewrite not_orP => -[]/(_ erefl).
  + by rewrite not_orP => -[]/(_ erefl).
  + by rewrite not_orP => -[]/(_ erefl).
- move: mUF.
  rewrite {1}/measurable /emeasurable /= => -[X mX [Y []]] {Y}.
  - rewrite setU0 => h.
    rewrite [X in measurable X](_ : _ = X) // predeqE => r; split => [|Xr].
      move=> -[n _ [x [Fnx xoo <-{r}]]].
      have : (\bigcup_n F n) x by exists n.
      by rewrite -h => -[x' Xx' <-].
    have [n _ Fnr] : (\bigcup_n F n) r%:E by rewrite -h; exists r.
    by exists n => //; exists r%:E => //; split => //; case.
  - move=> h.
    rewrite [X in measurable X](_ : _ = X) // predeqE => r; split => [|Xr].
      move=> -[n _ [x [Fnx xoo <-]]].
      have : (\bigcup_n F n) x by exists n.
      by rewrite -h => -[[x' Xx' <-//]|xoo']; move/not_orP : xoo => -[].
    have [n _ Fnr] : (\bigcup_n F n) r%:E by rewrite -h; left; exists r.
    by exists n => //; exists r%:E => //; split => //; case.
  - (* NB: almost the same as the previous one, factorize?*)
    move=> h.
    rewrite [X in measurable X](_ : _ = X) // predeqE => r; split => [|Xr].
      move=> -[n _ [x [Fnx xoo <-]]].
      have : (\bigcup_n F n) x by exists n.
      by rewrite -h => -[[x' Xx' <-//]|xoo']; move/not_orP : xoo => -[].
    have [n _ Fnr] : (\bigcup_n F n) r%:E by rewrite -h; left; exists r.
    by exists n => //; exists r%:E => //; split => //; case.
  - move=> h.
    rewrite [X in measurable X](_ : _ = X) // predeqE => r; split => [|Xr].
      move=> -[n _ [x [Fnx xoo <-]]].
      have : (\bigcup_n F n) x by exists n.
      by rewrite -h => -[[x' Xx' <-//]|].
    have [n _ Fnr] : (\bigcup_n F n) r%:E by rewrite -h; left; exists r.
    by exists n => //; exists r%:E => //; split => //; case.
Qed.

Definition elebesgue_measure_isMeasure : is_measure elebesgue_measure' :=
  Measure.Axioms elebesgue_measure'0 elebesgue_measure'_ge0
                 semi_sigma_additive_elebesgue_measure'.

Definition elebesgue_measure : {measure set \bar R -> \bar R} :=
  Measure.Pack _ elebesgue_measure_isMeasure.

End salgebra_R_ssets.
#[global]
Hint Extern 0 (measurable [set _]) => solve [apply: measurable_set1|
                                            apply: emeasurable_set1] : core.

Section measurable_fun_measurable.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (D : set T) (f : T -> \bar R).
Hypotheses (mD : measurable D) (mf : measurable_fun D f).
Implicit Types y : \bar R.

Lemma emeasurable_fun_c_infty y : measurable (D `&` [set x | y <= f x]).
Proof.
by rewrite -preimage_itv_c_infty; exact/mf/emeasurable_itv_bnd_pinfty.
Qed.

Lemma emeasurable_fun_o_infty y :  measurable (D `&` [set x | y < f x]).
Proof.
by rewrite -preimage_itv_o_infty; exact/mf/emeasurable_itv_bnd_pinfty.
Qed.

Lemma emeasurable_fun_infty_o y : measurable (D `&` [set x | f x < y]).
Proof.
by rewrite -preimage_itv_infty_o; exact/mf/emeasurable_itv_ninfty_bnd.
Qed.

Lemma emeasurable_fun_infty_c y : measurable (D `&` [set x | f x <= y]).
Proof.
by rewrite -preimage_itv_infty_c; exact/mf/emeasurable_itv_ninfty_bnd.
Qed.

Lemma emeasurable_fin_num : measurable (D `&` [set x | f x \is a fin_num]).
Proof.
rewrite [X in measurable X](_ : _ =
  \bigcup_k (D `&` ([set  x | - k%:R%:E <= f x] `&` [set x | f x <= k%:R%:E]))).
  apply: bigcupT_measurable => k; rewrite -(setIid D) setIACA.
  by apply: measurableI; [exact: emeasurable_fun_c_infty|
                          exact: emeasurable_fun_infty_c].
rewrite predeqE => t; split => [/= [Dt ft]|].
  have [ft0|ft0] := leP 0%R (fine (f t)).
    exists `|ceil (fine (f t))|%N => //=; split => //; split.
      by rewrite -{2}(fineK ft)// lee_fin (le_trans _ ft0)// ler_oppl oppr0.
    by rewrite natr_absz ger0_norm ?ceil_ge0// -(fineK ft) lee_fin ceil_ge.
  exists `|floor (fine (f t))|%N => //=; split => //; split.
    rewrite natr_absz ltr0_norm ?floor_lt0// EFinN.
    by rewrite -{2}(fineK ft) lee_fin mulrNz opprK floor_le.
  by rewrite -(fineK ft)// lee_fin (le_trans (ltW ft0)).
move=> [n _] [/= Dt [nft fnt]]; split => //; rewrite fin_numElt.
by rewrite (lt_le_trans _ nft) ?ltNye//= (le_lt_trans fnt)// ltey.
Qed.

Lemma emeasurable_neq y : measurable (D `&` [set x | f x != y]).
Proof.
rewrite (_ : [set x | f x != y] = f @^-1` (setT `\ y)).
  exact/mf/measurableD.
rewrite predeqE => t; split; last by rewrite /preimage /= => -[_ /eqP].
by rewrite /= => ft0; rewrite /preimage /=; split => //; exact/eqP.
Qed.

End measurable_fun_measurable.

Module RGenOInfty.
Section rgenoinfty.
Variable R : realType.
Implicit Types x y z : R.

Definition G := [set A | exists x, A = `]x, +oo[%classic].
Let T := g_measurableType G.

Lemma measurable_itv_bnd_infty b x :
  @measurable T [set` Interval (BSide b x) +oo%O].
Proof.
case: b; last by apply: sub_sigma_algebra; eexists; reflexivity.
rewrite itv_c_inftyEbigcap; apply: bigcapT_measurable => k.
by apply: sub_sigma_algebra; eexists; reflexivity.
Qed.

Lemma measurable_itv_bounded a b x : a != +oo%O ->
  @measurable T [set` Interval a (BSide b x)].
Proof.
case: a => [a r _|[_|//]].
  by rewrite set_itv_splitD; apply: measurableD => //;
    exact: measurable_itv_bnd_infty.
by rewrite -setCitvr; apply: measurableC; apply: measurable_itv_bnd_infty.
Qed.

Lemma measurableE :
  @measurable (g_measurableType (measurable : set (set (itvs R)))) =
  @measurable T.
Proof.
rewrite eqEsubset; split => A.
  apply: smallest_sub; first exact: smallest_sigma_algebra.
  by move=> I [x _ <-]; exact: measurable_itv_bounded.
apply: smallest_sub; first exact: smallest_sigma_algebra.
by move=> A' /= [x ->]; exact: measurable_itv.
Qed.

End rgenoinfty.
End RGenOInfty.

Module RGenInftyO.
Section rgeninftyo.
Variable R : realType.
Implicit Types x y z : R.

Definition G := [set A | exists x, A = `]-oo, x[%classic].
Let T := g_measurableType G.

Lemma measurable_itv_bnd_infty b x :
  @measurable T [set` Interval -oo%O (BSide b x)].
Proof.
case: b; first by apply sub_sigma_algebra; eexists; reflexivity.
rewrite -setCitvr itv_o_inftyEbigcup; apply/measurableC/bigcupT_measurable => n.
rewrite -setCitvl; apply: measurableC.
by apply: sub_sigma_algebra; eexists; reflexivity.
Qed.

Lemma measurable_itv_bounded a b x : a != -oo%O ->
  @measurable T [set` Interval (BSide b x) a].
Proof.
case: a => [a r _|[//|_]].
  by rewrite set_itv_splitD; apply/measurableD => //;
     rewrite -setCitvl; apply: measurableC; exact: measurable_itv_bnd_infty.
by rewrite -setCitvl; apply: measurableC; apply: measurable_itv_bnd_infty.
Qed.

Lemma measurableE :
  @measurable (g_measurableType (measurable : set (set (itvs R)))) =
  @measurable T.
Proof.
rewrite eqEsubset; split => A.
  apply: smallest_sub; first exact: smallest_sigma_algebra.
  by move=> I [x _ <-]; apply: measurable_itv_bounded.
apply: smallest_sub; first exact: smallest_sigma_algebra.
by move=> A' /= [x ->]; apply: measurable_itv.
Qed.

End rgeninftyo.
End RGenInftyO.

Module RGenCInfty.
Section rgencinfty.
Variable R : realType.
Implicit Types x y z : R.

Definition G : set (set R) := [set A | exists x, A = `[x, +oo[%classic].
Let T := g_measurableType G.

Lemma measurable_itv_bnd_infty b x :
  @measurable T [set` Interval (BSide b x) +oo%O].
Proof.
case: b; first by apply: sub_sigma_algebra; exists x; rewrite set_itv_c_infty.
rewrite itv_o_inftyEbigcup; apply: bigcupT_measurable => k.
by apply: sub_sigma_algebra; eexists; reflexivity.
Qed.

Lemma measurable_itv_bounded a b y : a != +oo%O ->
  @measurable T [set` Interval a (BSide b y)].
Proof.
case: a => [a r _|[_|//]].
  rewrite set_itv_splitD.
  by apply: measurableD; apply: measurable_itv_bnd_infty.
by rewrite -setCitvr; apply: measurableC; apply: measurable_itv_bnd_infty.
Qed.

Lemma measurableE :
  @measurable (g_measurableType (measurable : set (set (itvs R)))) =
  @measurable T.
Proof.
rewrite eqEsubset; split => A.
  apply: smallest_sub; first exact: smallest_sigma_algebra.
  by move=> I [x _ <-]; apply: measurable_itv_bounded.
apply: smallest_sub; first exact: smallest_sigma_algebra.
by move=> A' /= [x ->]; apply: measurable_itv.
Qed.

End rgencinfty.
End RGenCInfty.

Module RGenOpens.
Section rgenopens.

Variable R : realType.
Implicit Types x y z : R.

Definition G := [set A | exists x y, A = `]x, y[%classic].
Let T := g_measurableType G.

Local Lemma measurable_itvoo x y : @measurable T `]x, y[%classic.
Proof. by apply sub_sigma_algebra; eexists; eexists; reflexivity. Qed.

Local Lemma measurable_itv_o_infty x : @measurable T `]x, +oo[%classic.
Proof.
rewrite itv_bnd_inftyEbigcup; apply: bigcupT_measurable => i.
exact: measurable_itvoo.
Qed.

Lemma measurable_itv_bnd_infty b x :
  @measurable T [set` Interval (BSide b x) +oo%O].
Proof.
case: b; last exact: measurable_itv_o_infty.
rewrite itv_c_inftyEbigcap; apply: bigcapT_measurable => k.
exact: measurable_itv_o_infty.
Qed.

Lemma measurable_itv_infty_bnd b x :
  @measurable T [set` Interval -oo%O (BSide b x)].
Proof.
by rewrite -setCitvr; apply: measurableC; exact: measurable_itv_bnd_infty.
Qed.

Lemma measurable_itv_bounded a x b y :
  @measurable T [set` Interval (BSide a x) (BSide b y)].
Proof.
move: a b => [] []; rewrite -[X in measurable X]setCK setCitv;
  apply: measurableC; apply: measurableU; try solve[
    exact: measurable_itv_infty_bnd|exact: measurable_itv_bnd_infty].
Qed.

Lemma measurableE :
  @measurable (g_measurableType (measurable : set (set (itvs R)))) =
  @measurable T.
Proof.
rewrite eqEsubset; split => A.
  apply: smallest_sub; first exact: smallest_sigma_algebra.
  by move=> I [x _ <-]; apply: measurable_itv_bounded.
apply: smallest_sub; first exact: smallest_sigma_algebra.
by move=> A' /= [x [y ->]]; apply: measurable_itv.
Qed.

End rgenopens.
End RGenOpens.

Section erealwithrays.
Variable R : realType.
Implicit Types (x y z : \bar R) (r s : R).
Local Open Scope ereal_scope.

Lemma EFin_itv_bnd_infty b r : EFin @` [set` Interval (BSide b r) +oo%O] =
  [set` Interval (BSide b r%:E) +oo%O] `\ +oo.
Proof.
rewrite eqEsubset; split => [x [s /itvP rs <-]|x []].
  split => //=; rewrite in_itv /=.
  by case: b in rs *; rewrite /= ?(lee_fin, lte_fin) rs.
move: x => [s|_ /(_ erefl)|] //=; rewrite in_itv /= andbT; last first.
  by case: b => /=; rewrite 1?(leNgt,ltNge) 1?(ltNye, leNye).
by case: b => /=; rewrite 1?(lte_fin,lee_fin) => rs _;
  exists s => //; rewrite in_itv /= rs.
Qed.

Lemma EFin_itv r : [set s | r%:E < s%:E] = `]r, +oo[%classic.
Proof.
by rewrite predeqE => s; split => [|]; rewrite /= lte_fin in_itv/= andbT.
Qed.

Lemma preimage_EFin_setT : @EFin R @^-1` [set x | x \in `]-oo%E, +oo[] = setT.
Proof.
by rewrite set_itvE predeqE => r; split=> // _; rewrite /preimage /= ltNye.
Qed.

Lemma eitv_c_infty r : `[r%:E, +oo[%classic =
  \bigcap_k `](r - k.+1%:R^-1)%:E, +oo[%classic :> set _.
Proof.
rewrite predeqE => x; split=> [|].
- move: x => [s /=| _ n _|//].
  + rewrite in_itv /= andbT lee_fin => rs n _ /=.
    rewrite in_itv /= andbT lte_fin.
    by rewrite ltr_subl_addl (le_lt_trans rs)// ltr_addr invr_gt0.
  + by rewrite /= in_itv /= andbT ltey.
- move: x => [s| |/(_ 0%N Logic.I)] //=; last by rewrite in_itv /= leey.
  move=> h; rewrite in_itv /= lee_fin leNgt andbT; apply/negP.
  move=> /ltr_add_invr[k skr]; have {h} := h k Logic.I.
  rewrite /= in_itv /= andbT lte_fin ltNge => /negP; apply.
  by rewrite -ler_subl_addr opprK ltW.
Qed.

Lemma eitv_infty_c r : `]-oo, r%:E]%classic =
  \bigcap_k `]-oo, (r%:E + k.+1%:R^-1%:E)]%classic :> set _.
Proof.
rewrite predeqE => x; split=> [|].
- move: x => [s /=|//|_ n _].
  + rewrite in_itv /= lee_fin => sr n _; rewrite /= in_itv /=.
    by rewrite -EFinD lee_fin (le_trans sr)// ler_addl invr_ge0.
  + by rewrite /= in_itv /= -EFinD leNye.
- move: x => [s|/(_ 0%N Logic.I)//|]/=; rewrite ?in_itv /= ?leNye//.
  move=> h; rewrite lee_fin leNgt; apply/negP => /ltr_add_invr[k rks].
  have {h} := h k Logic.I; rewrite /= in_itv /=.
  by rewrite -EFinD lee_fin leNgt => /negP; apply.
Qed.

Lemma eset1_ninfty :
  [set -oo] = \bigcap_k `]-oo, (-k%:R%:E)[%classic :> set (\bar R).
Proof.
rewrite eqEsubset; split=> [_ -> i _ |]; first by rewrite /= in_itv /= ltNye.
move=> [r|/(_ O Logic.I)|]//.
move=> /(_ `|floor r|%N Logic.I); rewrite /= in_itv/= ltNge.
rewrite lee_fin; have [r0|r0] := leP 0%R r.
  by rewrite (le_trans _ r0) // ler_oppl oppr0 ler0n.
rewrite ler_oppl -abszN natr_absz gtr0_norm; last first.
  by rewrite ltr_oppr oppr0 floor_lt0.
by rewrite mulrNz ler_oppl opprK floor_le.
Qed.

Lemma eset1_pinfty :
  [set +oo] = \bigcap_k `]k%:R%:E, +oo[%classic :> set (\bar R).
Proof.
rewrite eqEsubset; split=> [_ -> i _/=|]; first by rewrite in_itv /= ltey.
move=> [r| |/(_ O Logic.I)] // /(_ `|ceil r|%N Logic.I); rewrite /= in_itv /=.
rewrite andbT lte_fin ltNge.
have [r0|r0] := ltP 0%R r; last by rewrite (le_trans r0).
by rewrite natr_absz gtr0_norm // ?ceil_ge// ceil_gt0.
Qed.

End erealwithrays.

Module ErealGenOInfty.
Section erealgenoinfty.
Variable R : realType.
Implicit Types (x y z : \bar R) (r s : R).

Local Open Scope ereal_scope.

Definition G := [set A : set \bar R | exists x, A = `]x, +oo[%classic].
Let T := g_measurableType G.

Lemma measurable_set1_ninfty : @measurable T [set -oo].
Proof.
rewrite eset1_ninfty; apply: (@bigcapT_measurable T) => i.
rewrite -setCitvr; apply: measurableC; rewrite eitv_c_infty.
apply: bigcapT_measurable => j; apply: sub_sigma_algebra.
by exists (- (i%:R + j.+1%:R^-1))%:E; rewrite opprD.
Qed.

Lemma measurable_set1_pinfty : @measurable T [set +oo].
Proof.
rewrite eset1_pinfty; apply: bigcapT_measurable => i.
by apply: sub_sigma_algebra; exists i%:R%:E.
Qed.

Lemma measurableE : emeasurable (measurable : set (set (itvs R))) = @measurable T.
Proof.
apply/seteqP; split; last first.
  apply: smallest_sub.
    split; first exact: emeasurable0.
      by move=> *; rewrite setTD; exact: emeasurableC.
    by move=> *; exact: bigcupT_emeasurable.
  move=> _ [x ->]; rewrite /emeasurable /=; move: x => [r| |].
  + exists `]r, +oo[%classic.
      rewrite RGenOInfty.measurableE.
      exact: RGenOInfty.measurable_itv_bnd_infty.
    by exists [set +oo]; [constructor|rewrite -punct_eitv_bnd_pinfty].
  + exists set0 => //.
    by exists set0; [constructor|rewrite setU0 itv_opinfty_pinfty image_set0].
  + exists setT => //; exists [set +oo]; first by constructor.
    by rewrite itv_oninfty_pinfty punct_eitv_setTR.
move=> A [B mB [C mC]] <-; apply: measurableU; last first.
  case: mC; [by []|exact: measurable_set1_ninfty
                  |exact: measurable_set1_pinfty|].
  - by apply: measurableU; [exact: measurable_set1_ninfty|
                            exact: measurable_set1_pinfty].
rewrite RGenOInfty.measurableE in mB.
have smB := smallest_sub _ _ mB.
(* BUG: elim/smB : _. fails !! *)
apply: (smB (@measurable T \o (image^~ EFin))); last first.
  move=> _ [r ->]/=; rewrite EFin_itv_bnd_infty; apply: measurableD.
    by apply sub_sigma_algebra => /=; exists r%:E.
  exact: measurable_set1_pinfty.
split=> /= [|D mD|F mF]; first by rewrite image_set0.
- rewrite setTD EFin_setC; apply: measurableD; first exact: measurableC.
  by apply: measurableU; [exact: measurable_set1_ninfty|
                          exact: measurable_set1_pinfty].
- by rewrite EFin_bigcup; apply: bigcupT_measurable => i; exact: mF.
Qed.

End erealgenoinfty.
End ErealGenOInfty.

Module ErealGenCInfty.
Section erealgencinfty.
Variable R : realType.
Implicit Types (x y z : \bar R) (r s : R).
Local Open Scope ereal_scope.

Definition G := [set A : set \bar R | exists x, A = `[x, +oo[%classic].
Let T := g_measurableType G.

Lemma measurable_set1_ninfty : @measurable T [set -oo].
Proof.
rewrite eset1_ninfty; apply: bigcapT_measurable=> i; rewrite -setCitvr.
by apply: measurableC; apply: sub_sigma_algebra; exists (- i%:R)%:E.
Qed.

Lemma measurable_set1_pinfty : @measurable T [set +oo].
Proof.
apply: sub_sigma_algebra; exists +oo; rewrite predeqE => x; split => [->//|/=].
by rewrite in_itv /= andbT lee_pinfty_eq => /eqP ->.
Qed.

Lemma measurableE : emeasurable (measurable : set (set (itvs R))) = @measurable T.
Proof.
apply/seteqP; split; last first.
  apply: smallest_sub.
    split; first exact: emeasurable0.
      by move=> *; rewrite setTD; exact: emeasurableC.
    by move=> *; exact: bigcupT_emeasurable.
  move=> _ [[r||] ->]/=.
  - exists `[r, +oo[%classic.
      rewrite RGenOInfty.measurableE.
      exact: RGenOInfty.measurable_itv_bnd_infty.
    by exists [set +oo]; [constructor | rewrite -punct_eitv_bnd_pinfty].
   - exists set0 => //; exists [set +oo]; first by constructor.
     by rewrite image_set0 set0U itv_cpinfty_pinfty.
   - exists setT => //; exists [set -oo; +oo]; first by constructor.
     by rewrite itv_cninfty_pinfty setUA punct_eitv_setTL setUCl.
move=> _ [A' mA' [C mC]] <-; apply: measurableU; last first.
  case: mC; [by []|exact: measurable_set1_ninfty|
                   exact: measurable_set1_pinfty|].
  by apply: measurableU; [exact: measurable_set1_ninfty|
                          exact: measurable_set1_pinfty].
rewrite RGenCInfty.measurableE in mA'.
have smA' := smallest_sub _ _ mA'.
(* BUG: elim/smA' : _. fails !! *)
apply: (smA' (@measurable T \o (image^~ EFin))); last first.
  move=> _ [r ->]/=; rewrite EFin_itv_bnd_infty; apply: measurableD.
    by apply sub_sigma_algebra => /=; exists r%:E.
  exact: measurable_set1_pinfty.
split=> /= [|D mD|F mF]; first by rewrite image_set0.
- rewrite setTD EFin_setC; apply: measurableD; first exact: measurableC.
  by apply: measurableU; [exact: measurable_set1_ninfty|
                          exact: measurable_set1_pinfty].
- by rewrite EFin_bigcup; apply: bigcupT_measurable => i; exact: mF.
Qed.

End erealgencinfty.
End ErealGenCInfty.

Section trace.
Variable (T : Type).
Implicit Types (G : set (set T)) (A D : set T).

(* intended as a trace sigma-algebra *)
Definition strace G D := [set x `&` D | x in G].

Lemma stracexx G D : G D -> strace G D D.
Proof. by rewrite /strace /=; exists D => //; rewrite setIid. Qed.

Lemma sigma_algebra_strace G D :
  sigma_algebra setT G -> sigma_algebra D (strace G D).
Proof.
move=> [G0 GC GU]; split; first by exists set0 => //; rewrite set0I.
- move=> S [A mA ADS]; have mCA := GC _ mA.
  have : strace G D (D `&` ~` A).
    by rewrite setIC; exists (setT `\` A) => //; rewrite setTD.
  rewrite -setDE => trDA.
  have DADS : D `\` A = D `\` S by rewrite -ADS !setDE setCI setIUr setICr setU0.
  by rewrite DADS in trDA.
- move=> S mS; have /choice[M GM] : forall n, exists A, G A /\ S n = A `&` D.
    by move=> n; have [A mA ADSn] := mS n; exists A.
  exists (\bigcup_i (M i)); first by apply GU => i;  exact: (GM i).1.
  by rewrite setI_bigcupl; apply eq_bigcupr => i _; rewrite (GM i).2.
Qed.

End trace.

Lemma strace_measurable (T : measurableType) (A : set T) : measurable A ->
  strace measurable A `<=` measurable.
Proof. by move=> mA=> _ [C mC <-]; apply: measurableI. Qed.

(* more properties of measurable functions *)

Lemma is_interval_measurable (R : realType) (I : set R) :
  is_interval I -> measurable I.
Proof. by move/is_intervalP => ->; exact: measurable_itv. Qed.

Section coutinuous_measurable.
Variable R : realType.

Lemma open_measurable (U : set R) : open U -> measurable U.
Proof.
move=> /open_bigcup_rat ->; rewrite bigcup_mkcond; apply: bigcupT_measurable_rat.
move=> q; case: ifPn => // qfab; apply: is_interval_measurable => //.
exact: is_interval_bigcup_ointsub.
Qed.

Lemma continuous_measurable_fun (f : R -> R) : continuous f ->
  measurable_fun setT f.
Proof.
move=> /continuousP cf; apply: (measurability (RGenOpens.measurableE R)).
move=> _ [_ [a [b ->] <-]]; rewrite setTI.
by apply: open_measurable; exact/cf/interval_open.
Qed.

End coutinuous_measurable.

Section standard_measurable_fun.

Lemma measurable_fun_normr (R : realType) (D : set R) :
  measurable_fun D (@normr _ R).
Proof.
move=> mD; apply: (measurability (RGenOInfty.measurableE R)) => //.
move=> /= _ [_ [x ->] <-]; apply: measurableI => //.
have [x0|x0] := leP 0 x.
  rewrite [X in measurable X](_ : _ = `]-oo, (- x)[ `|` `]x, +oo[)%classic.
    by apply: measurableU; apply: measurable_itv.
  rewrite predeqE => r; split => [|[|]]; rewrite preimage_itv ?in_itv ?andbT/=.
  - have [r0|r0] := leP 0 r; [rewrite ger0_norm|rewrite ltr0_norm] => // xr;
      rewrite 2!in_itv/=.
    + by right; rewrite xr.
    + by left; rewrite ltr_oppr.
  - move=> rx /=.
    by rewrite ler0_norm 1?ltr_oppr// (le_trans (ltW rx))// ler_oppl oppr0.
  - by rewrite in_itv /= andbT => xr; rewrite (lt_le_trans _ (ler_norm _)).
rewrite [X in measurable X](_ : _ = setT)// predeqE => r.
by split => // _; rewrite /= in_itv /= andbT (lt_le_trans x0).
Qed.

End standard_measurable_fun.

Section measurable_fun_realType.
Variables (T : measurableType) (R : realType).
Implicit Types (D : set T) (f g : T -> R).

Lemma measurable_funD D f g :
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \+ g).
Proof.
move=> mf mg mD; apply: (measurability (RGenOInfty.measurableE R)) => //.
move=> /= _ [_ [a ->] <-]; rewrite preimage_itv_o_infty.
rewrite [X in measurable X](_ : _ = \bigcup_(q : rat)
  ((D `&` [set x | ratr q < f x]) `&` (D `&` [set x | a - ratr q < g x]))).
  apply: bigcupT_measurable_rat => q; apply: measurableI.
  - by rewrite -preimage_itv_o_infty; apply: mf => //; apply: measurable_itv.
  - by rewrite -preimage_itv_o_infty; apply: mg => //; apply: measurable_itv.
rewrite predeqE => x; split => [|[r _] []/= [Dx rfx]] /= => [[Dx]|[_]].
  rewrite -ltr_subl_addr => /rat_in_itvoo[r]; rewrite inE /= => /itvP h.
  exists r => //; rewrite setIACA setIid; split => //; split => /=.
    by rewrite h.
  by rewrite ltr_subl_addr addrC -ltr_subl_addr h.
by rewrite ltr_subl_addr=> afg; rewrite (lt_le_trans afg)// addrC ler_add2r ltW.
Qed.

Lemma measurable_funrM D f (k : R) : measurable_fun D f ->
  measurable_fun D (fun x => k * f x).
Proof.
apply: (@measurable_fun_comp _ _ _ ( *%R k)).
by apply: continuous_measurable_fun; apply: mulrl_continuous.
Qed.

Lemma measurable_funN D f : measurable_fun D f -> measurable_fun D (-%R \o f).
Proof.
move=> mf mD; rewrite (_ : _ \o _ = (fun x => - 1 * f x)).
  exact: measurable_funrM.
by under eq_fun do rewrite mulN1r.
Qed.

Lemma measurable_funB D f g : measurable_fun D f ->
  measurable_fun D g -> measurable_fun D (f \- g).
Proof.
by move=> ? ? ?; apply: measurable_funD => //; exact: measurable_funN.
Qed.

Lemma measurable_fun_exprn D n f :
  measurable_fun D f -> measurable_fun D (fun x => f x ^+ n).
Proof.
apply: measurable_fun_comp ((@GRing.exp R)^~ n) _ _ _.
by apply: continuous_measurable_fun; apply: exprn_continuous.
Qed.

Lemma measurable_fun_sqr D f :
  measurable_fun D f -> measurable_fun D (fun x => f x ^+ 2).
Proof. exact: measurable_fun_exprn. Qed.

Lemma measurable_funM D f g :
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \* g).
Proof.
move=> mf mg mD; rewrite (_ : (_ \* _) = (fun x => 2%:R^-1 * (f x + g x) ^+ 2)
  \- (fun x => 2%:R^-1 * (f x ^+ 2)) \- (fun x => 2%:R^-1 * ( g x ^+ 2))).
  apply: measurable_funB => //; last first.
    by apply: measurable_funrM => //; exact: measurable_fun_sqr.
  apply: measurable_funB => //; last first.
    by apply: measurable_funrM => //; exact: measurable_fun_sqr.
  apply: measurable_funrM => //.
  by apply: measurable_fun_sqr => //; exact: measurable_funD.
rewrite funeqE => x /=; rewrite -2!mulrBr sqrrD (addrC (f x ^+ 2)) -addrA.
rewrite -(addrA (f x * g x *+ 2)) -opprB opprK (addrC (g x ^+ 2)) addrK.
by rewrite -(mulr_natr (f x * g x)) -(mulrC 2) mulrA mulVr ?mul1r// unitfE.
Qed.

Lemma measurable_fun_max  D f g :
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \max g).
Proof.
move=> mf mg mD; apply (measurability (RGenCInfty.measurableE R)) => //.
move=> _ [_ [x ->] <-]; rewrite [X in measurable X](_ : _ =
    (D `&` f @^-1` `[x, +oo[) `|` (D `&` g @^-1` `[x, +oo[)); last first.
  rewrite predeqE => t /=; split.
    by rewrite /= !in_itv /= !andbT le_maxr => -[Dx /orP[|]]; tauto.
  by move=> [|]; rewrite !in_itv/= !andbT le_maxr => -[Dx ->]//; rewrite orbT.
by apply: measurableU; [apply: mf|apply: mg] =>//; apply: measurable_itv.
Qed.

Lemma measurable_fun_sups D (h : (T -> R)^nat) n :
  (forall t, D t -> has_ubound (range (h ^~ t))) ->
  (forall m, measurable_fun D (h m)) ->
  measurable_fun D (fun x => sups (h ^~ x) n).
Proof.
move=> f_ub mf mD; apply: (measurability (RGenOInfty.measurableE R)) => //.
move=> _ [_ [x ->] <-]; rewrite sups_preimage // setI_bigcupr.
by apply: bigcup_measurable => k /= nk; apply: mf => //; exact: measurable_itv.
Qed.

Lemma measurable_fun_infs D (h : (T -> R)^nat) n :
  (forall t, D t -> has_lbound (range (h ^~ t))) ->
  (forall n, measurable_fun D (h n)) ->
  measurable_fun D (fun x => infs (h ^~ x) n).
Proof.
move=> lb_f mf mD; apply: (measurability (RGenInftyO.measurableE R)) =>//.
move=> _ [_ [x ->] <-]; rewrite infs_preimage // setI_bigcupr.
by apply: bigcup_measurable => k /= nk; apply: mf => //; exact: measurable_itv.
Qed.

Lemma measurable_fun_lim_sup D (h : (T -> R)^nat) :
  (forall t, D t -> has_ubound (range (h ^~ t))) ->
  (forall t, D t -> has_lbound (range (h ^~ t))) ->
  (forall n, measurable_fun D (h n)) ->
  measurable_fun D (fun x => lim_sup (h ^~ x)).
Proof.
move=> f_ub f_lb mf.
have : {in D, (fun x => inf [set sups (h ^~ x) n | n in [set n | 0 <= n]%N])
              =1 (fun x => lim_sup (h^~ x))}.
  move=> t; rewrite inE => Dt; apply/esym/cvg_lim; first exact: Rhausdorff.
  rewrite [X in _ --> X](_ : _ = inf (range (sups (h^~t)))).
    by apply: cvg_sups_inf; [exact: f_ub|exact: f_lb].
  by congr (inf [set _ | _ in _]); rewrite predeqE.
move/eq_measurable_fun; apply; apply: measurable_fun_infs => //.
  move=> t Dt; have [M hM] := f_lb _ Dt; exists M => _ [m /= nm <-].
  rewrite (@le_trans _ _ (h m t)) //; first by apply hM => /=; exists m.
  by apply: sup_ub; [exact/has_ubound_sdrop/f_ub|exists m => /=].
by move=> k; exact: measurable_fun_sups.
Qed.

Lemma measurable_fun_cvg D (h : (T -> R)^nat) f :
  (forall m, measurable_fun D (h m)) -> (forall x, D x -> h ^~ x --> f x) ->
  measurable_fun D f.
Proof.
move=> mf_ f_f; have fE x : D x -> f x = lim_sup (h ^~ x).
  move=> Dx; have /cvg_lim  <-// := @cvg_sups _ (h ^~ x) (f x) (f_f _ Dx).
  exact: Rhausdorff.
apply: (@eq_measurable_fun _ _ D (fun x => lim_sup (h ^~ x))).
  by move=> x; rewrite inE => Dx; rewrite -fE.
apply: (@measurable_fun_lim_sup _ h) => // t Dt.
- apply/bounded_fun_has_ubound/(@cvg_seq_bounded _ [normedModType R of R^o]).
  by apply/cvg_ex; eexists; exact: f_f.
- apply/bounded_fun_has_lbound/(@cvg_seq_bounded _ [normedModType R of R^o]).
  by apply/cvg_ex; eexists; exact: f_f.
Qed.

End measurable_fun_realType.

Section standard_emeasurable_fun.
Variable R : realType.

Lemma measurable_fun_EFin (D : set R) : measurable_fun D EFin.
Proof.
move=> mD; apply: (measurability (ErealGenOInfty.measurableE R)) => //.
move=> /= _ [_ [x ->]] <-; move: x => [x| |]; apply: measurableI => //.
- by rewrite preimage_itv_o_infty EFin_itv; exact: measurable_itv.
- by rewrite [X in measurable X](_ : _ = set0)// predeqE.
- by rewrite preimage_EFin_setT.
Qed.

Lemma measurable_fun_abse (D : set (\bar R)) : measurable_fun D abse.
Proof.
move=> mD; apply: (measurability (ErealGenOInfty.measurableE R)) => //.
move=> /= _ [_ [x ->] <-]; move: x => [x| |].
- rewrite [X in _ @^-1` X](punct_eitv_bnd_pinfty _ x) preimage_setU setIUr.
  apply: measurableU; last first.
    rewrite preimage_abse_pinfty.
    by apply: measurableI => //; exact: measurableU.
  apply: measurableI => //; exists (normr @^-1` `]x, +oo[%classic).
    rewrite -[X in measurable X]setTI.
    by apply: measurable_fun_normr => //; exact: measurable_itv.
  exists set0; first by constructor.
  rewrite setU0 predeqE => -[y| |]; split => /= => -[r];
    rewrite ?/= /= ?in_itv /= ?andbT => xr//.
    + by move=> [ry]; exists `|y| => //=; rewrite in_itv/= andbT -ry.
    + by move=> [ry]; exists y => //=; rewrite /= in_itv/= andbT -ry.
- by apply: measurableI => //; rewrite itv_opinfty_pinfty preimage_set0.
- apply: measurableI => //; rewrite itv_oninfty_pinfty -preimage_setC.
  by apply: measurableC; rewrite preimage_abse_ninfty.
Qed.

Lemma emeasurable_fun_minus (D : set (\bar R)) :
  measurable_fun D (-%E : \bar R -> \bar R).
Proof.
move=> mD; apply: (measurability (ErealGenCInfty.measurableE R)) => //.
move=> _ [_ [x ->] <-]; rewrite (_ : _ @^-1` _ = `]-oo, (- x)%E]%classic).
  by apply: measurableI => //; exact: emeasurable_itv_ninfty_bnd.
by rewrite predeqE => y; rewrite preimage_itv !in_itv/= andbT in_itv lee_oppr.
Qed.

End standard_emeasurable_fun.
#[global] Hint Extern 0 (measurable_fun _ abse) =>
  solve [exact: measurable_fun_abse] : core.
#[global] Hint Extern 0 (measurable_fun _ EFin) =>
  solve [exact: measurable_fun_EFin] : core.

(* NB: real-valued function *)
Lemma EFin_measurable_fun (T : measurableType) (R : realType) (D : set T)
    (g : T -> R) :
  measurable_fun D (EFin \o g) <-> measurable_fun D g.
Proof.
split=> [mf mD A mA|]; last by move=> mg; exact: measurable_fun_comp.
rewrite [X in measurable X](_ : _ = D `&` (EFin \o g) @^-1` (EFin @` A)).
  by apply: mf => //; exists A => //; exists set0; [constructor|rewrite setU0].
congr (_ `&` _);rewrite eqEsubset; split=> [|? []/= _ /[swap] -[->//]].
by move=> ? ?; exact: preimage_image.
Qed.

Section emeasurable_fun.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Implicit Types (D : set T).

Lemma measurable_fun_einfs D (f : (T -> \bar R)^nat) :
  (forall n, measurable_fun D (f n)) ->
  forall n, measurable_fun D (fun x => einfs (f ^~ x) n).
Proof.
move=> mf n mD.
apply: (measurability (ErealGenCInfty.measurableE R)) => //.
move=> _ [_ [x ->] <-]; rewrite einfs_preimage -bigcapIr; last by exists n => /=.
by apply: bigcap_measurable => ? ?; exact/mf/emeasurable_itv_bnd_pinfty.
Qed.

Lemma measurable_fun_esups D (f : (T -> \bar R)^nat) :
  (forall n, measurable_fun D (f n)) ->
  forall n, measurable_fun D (fun x => esups (f ^~ x) n).
Proof.
move=> mf n mD; apply: (measurability (ErealGenOInfty.measurableE R)) => //.
move=> _ [_ [x ->] <-];rewrite esups_preimage setI_bigcupr.
by apply: bigcup_measurable => ? ?; exact/mf/emeasurable_itv_bnd_pinfty.
Qed.

Lemma emeasurable_fun_max D (f g : T -> \bar R) :
  measurable_fun D f -> measurable_fun D g ->
  measurable_fun D (fun x => maxe (f x) (g x)).
Proof.
move=> mf mg mD; apply: (measurability (ErealGenCInfty.measurableE R)) => //.
move=> _ [_ [x ->] <-]; rewrite [X in measurable X](_ : _ =
    (D `&` f @^-1` `[x, +oo[) `|` (D `&` g @^-1` `[x, +oo[)); last first.
  rewrite predeqE => t /=; split.
    by rewrite !/= /= !in_itv /= !andbT le_maxr => -[Dx /orP[|]];
      tauto.
  by move=> [|]; rewrite !/= /= !in_itv/= !andbT le_maxr;
    move=> [Dx ->]//; rewrite orbT.
by apply: measurableU; [exact/mf/emeasurable_itv_bnd_pinfty|
                        exact/mg/emeasurable_itv_bnd_pinfty].
Qed.

Lemma emeasurable_fun_funenng D (f : T -> \bar R) :
  measurable_fun D f -> measurable_fun D f^\+.
Proof.
by move=> mf; apply: emeasurable_fun_max => //; apply: measurable_fun_cst.
Qed.

Lemma emeasurable_fun_funennp D (f : T -> \bar R) :
  measurable_fun D f -> measurable_fun D f^\-.
Proof.
move=> mf; apply: emeasurable_fun_max => //; last exact: measurable_fun_cst.
by apply: measurable_fun_comp => //; apply: emeasurable_fun_minus.
Qed.

Lemma emeasurable_fun_min D (f g : T -> \bar R) :
  measurable_fun D f -> measurable_fun D g ->
  measurable_fun D (fun x => mine (f x) (g x)).
Proof.
move=> mf mg mD; apply: (measurability (ErealGenCInfty.measurableE R)) => //.
move=> _ [_ [x ->] <-]; rewrite [X in measurable X](_ : _ =
    (D `&` f @^-1` `[x, +oo[) `&` (D `&` g @^-1` `[x, +oo[)); last first.
  rewrite predeqE => t /=; split.
    rewrite !/= !in_itv /= !andbT le_minr => -[Dt /andP[xft xgt]].
    tauto.
  move=> []; rewrite !/= !in_itv/= !andbT le_minr=> -[Dt xft [_ xgt]].
  by split => //; rewrite xft xgt.
by apply: measurableI; [exact/mf/emeasurable_itv_bnd_pinfty|
                        exact/mg/emeasurable_itv_bnd_pinfty].
Qed.

Lemma measurable_fun_elim_sup D (f : (T -> \bar R)^nat) :
  (forall n, measurable_fun D (f n)) ->
  measurable_fun D (fun x => elim_sup (f ^~ x)).
Proof.
move=> mf mD; rewrite (_ :  (fun _ => _) =
    (fun x => ereal_inf [set esups (f^~ x) n | n in [set n | n >= 0]%N])).
  by apply: measurable_fun_einfs => // k; exact: measurable_fun_esups.
rewrite funeqE => t; apply/cvg_lim => //.
rewrite [X in _ --> X](_ : _ = ereal_inf (range (esups (f^~t)))).
  exact: cvg_esups_inf.
by congr (ereal_inf [set _ | _ in _]); rewrite predeqE.
Qed.

Lemma emeasurable_fun_cvg D (f_ : (T -> \bar R)^nat) (f : T -> \bar R) :
  (forall m, measurable_fun D (f_ m)) ->
  (forall x, D x -> f_ ^~ x --> f x) -> measurable_fun D f.
Proof.
move=> mf_ f_f; have fE x : D x -> f x = elim_sup (f_^~ x).
  by move=> Dx; have /cvg_lim  <-// := @cvg_esups _ (f_^~x) (f x) (f_f x Dx).
apply: (measurable_fun_ext (fun x => elim_sup (f_ ^~ x))) => //.
  by move=> x; rewrite inE => Dx; rewrite fE.
exact: measurable_fun_elim_sup.
Qed.

End emeasurable_fun.
Arguments emeasurable_fun_cvg {T R D} f_.
