(* -*- company-coq-local-symbols: (("`&`" . ?∩) ("`|`" . ?∪) ("set0" . ?∅)); -*- *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
Require Import boolp reals ereal classical_sets signed topology numfun.
Require Import mathcomp_extra functions normedtype.
From HB Require Import structures.
Require Import sequences esum measure fsbigop cardinality set_interval.
Require Import realfun.

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
rewrite esum_ge//; exists [set` X] => //; rewrite fsbig_finite// ?set_fsetK//=.
rewrite lee_sum // => k _; rewrite ?AE// !hlength_itv/= ?lte_fin -?EFinD/=.
by case: ifPn => ?; rewrite ?add0e ?lee_add2l// lee_fin ler_subl_addl natrX De.
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
Abort.

Let lebesgue_stieltjes_measure_set1 (a : R) :
  m [set a] = ((f a)%:E - (lim (f @ at_left a))%:E)%E.
Proof.
(*rewrite (set1Ebigcap a).*)
Abort.

Let lebesgue_stieltjes_measure_itvoo (a b : R) : a <= b ->
  m `]a, b[%classic = ((lim (f @ at_left b))%:E - (f a)%:E)%E.
Proof.
Abort.

Let lebesgue_stieltjes_measure_itvcc (a b : R) : a <= b ->
  m `[a, b]%classic = ((f b)%:E - (lim (f @ at_left a))%:E)%E.
Proof.
Abort.

Let lebesgue_stieltjes_measure_itvco (a b : R) : a <= b ->
  m `[a, b[%classic = ((lim (f @ at_left b))%:E - (lim (f @ at_left a))%:E)%E.
Proof.
Abort.


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

HB.structure Definition FiniteSignedMeasure d
    (R : numFieldType) (T : semiRingOfSetsType d) := {
  mu of isFiniteSignedMeasure d R T mu }.

HB.mixin Record isAdditiveSignedMeasure d (R : numFieldType)
    (T : semiRingOfSetsType d) mu of isFiniteSignedMeasure d R T mu := {
  smeasure_semi_additive : semi_additive mu }.

HB.structure Definition AdditiveSignedMeasure d (R : numFieldType)
    (T : semiRingOfSetsType d) :=
  { mu of isAdditiveSignedMeasure d R T mu & FiniteSignedMeasure d mu }.

Notation additive_smeasure := AdditiveSignedMeasure.type.
Notation "{ 'additive_smeasure' 'set' T '->' '\bar' R }" :=
  (additive_smeasure R T) (at level 36, T, R at next level,
    format "{ 'additive_smeasure'  'set'  T  '->'  '\bar'  R }") : ring_scope.

HB.mixin Record isSignedMeasure0 d (R : numFieldType) (T : semiRingOfSetsType d)
    mu of isAdditiveSignedMeasure d R T mu & isFiniteSignedMeasure d R T mu := {
  smeasure_semi_sigma_additive : semi_sigma_additive mu }.

HB.structure Definition SignedMeasure d (R : numFieldType)
    (T : semiRingOfSetsType d) :=
  { mu of isSignedMeasure0 d R T mu & AdditiveSignedMeasure d mu }.

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
Abort.

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

Lemma s_measureD d (R : realType) (X : measurableType d)
   (mu : {smeasure set X -> \bar R}) (A B : set X) :
  measurable A -> measurable B ->
    (*mu A < +oo ->*) mu (A `\` B) = mu A - mu (A `&` B).
Proof.
move=> mA mB.
rewrite (s_measureDI mu mA mB) addeK// fin_numE 1?gt_eqF 1?lt_eqF//.
- rewrite ltey_eq.
  rewrite isfinite //.
  exact:measurableI.
- rewrite ltNye_eq.
  rewrite isfinite//.
  exact:measurableI.
Qed.

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

Lemma subsetC_trivIset (X : Type) (A : nat -> set X) :
  (forall n, A n.+1 `<=` ~` \big[setU/set0]_(i < n.+1) A i) ->
  trivIset setT A.
Proof.
move=> PFkU.
apply: lt_trivIset => n.
have [m] := ubnP n; elim: m n => //= m IHm [_ []//|n] /=.
rewrite ltnS => nm k; rewrite ltnS => kn; move: kn IHm.
rewrite leq_eqVlt => /orP[/eqP -> IHm|kn IHm].
  rewrite setIC; apply/disjoints_subset.
  move: n nm => [m0|n nm].
    have := PFkU O.
    rewrite big_ord_recr/= big_ord0 set0U.
    move/subset_trans; apply.
    rewrite -setTD.
    by apply: setDSS => //.
  have K1 := PFkU n.+1.
  apply (subset_trans K1).
  apply: subsetC.
  rewrite big_ord_recr/=.
  exact: subsetUr.
have {}IHm := IHm _ nm _ kn.
rewrite setIC; apply/disjoints_subset.
have K1 := PFkU n.
apply (subset_trans K1).
apply: subsetC.
rewrite big_ord_recr/=.
rewrite -(bigcup_mkord _ A).
apply: (subset_trans _ (@subsetUl _ _ _)).
by apply: bigcup_sup.
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
    apply: (contra_not (nset0 (S `\` _))).
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
  apply: subsetC_trivIset => n /=.
  have [K1 _] := PFkU n.
  apply (subset_trans K1).
  rewrite -setTD.
  apply: setDSS => //.
  rewrite Ubig.
  by rewrite big_ord_recr/=.
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

Lemma negative_set_smeasure0 d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
  forall N, negative_set nu N -> nu N <= 0.
Proof.
move=> N [mN negN].
by apply negN.
Qed.

Definition s_mrestr d (T : measurableType d) (R : realFieldType) (D : set T)
  (f : set T -> \bar R) (mD : measurable D) := fun X => f (X `&` D).

Section s_measure_restr.
Variables (d : _) (T : measurableType d) (R : realFieldType).
Variables (mu : {smeasure set T -> \bar R}) (D : set T) (mD : measurable D).

Local Notation restr := (s_mrestr mu mD).

Let s_restr_isfinite U : measurable U -> restr U \is a fin_num.
Proof.
move=> mU.
by have /(@isfinite _ _ _ mu) : measurable (U `&` D) by exact: measurableI.
Qed.

HB.instance Definition _ :=
  isFiniteSignedMeasure.Build _ _ _ restr s_restr_isfinite.

Let s_restr_smeasure_semi_additive : semi_additive restr.
Proof.
move=> F n mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
rewrite -(smeasure_semi_additive _ _ mFD)//; last exact: bigsetU_measurable.
by rewrite /s_mrestr /FD big_distrl.
Qed.

HB.instance Definition _ :=
  isAdditiveSignedMeasure.Build _ _ _ restr s_restr_smeasure_semi_additive.

Let s_restr_smeasure_semi_sigma_additive : semi_sigma_additive restr.
Proof.
move=> F mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
rewrite /restr setI_bigcupl; apply: smeasure_semi_sigma_additive => //.
by apply: bigcup_measurable => k _; exact: measurableI.
Qed.

HB.instance Definition _ :=
  isSignedMeasure0.Build _ _ _ restr s_restr_smeasure_semi_sigma_additive.

End s_measure_restr.

Lemma positive_set_0' d (X : measurableType d) (R : realType) (P : set X)
    (mP : measurable P) (nu : {smeasure set X -> \bar R}) :
  (forall N, measurable N -> negative_set nu (N `&` P) -> s_mrestr nu mP N = 0) ->
    forall S, S \in measurable -> S `<=` P -> s_mrestr nu mP S >= 0.
Proof.
move=> h S /[1!inE] mS SP.
pose mu := [the smeasure _ _ of s_mrestr nu mP].
have : forall N, negative_set mu N -> mu N = 0.
  move=> N [/[1!inE] mN Nmu]; rewrite /mu/= h//; split=> [|E /[1!inE] mE ENP].
    by rewrite inE; exact: measurableI.
  have : E `&` P `<=` N by move=> x [Ex Px]; have [] := ENP x Ex.
  have : measurable (E `&` P) by exact: measurableI.
  rewrite -inE => /Nmu /[apply].
  rewrite /mu/= /s_mrestr/=.
  suff -> : E `&` P `&` P = E by [].
  rewrite -setIA setIid; apply/seteqP; split=> [x []//|x Ex].
  by have [] := ENP _ Ex.
by move/(@positive_set_0 _ _ _ mu); apply; rewrite inE.
Qed.

Lemma negative_set0 d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) : negative_set nu set0.
Proof.
rewrite /negative_set.
rewrite inE.
split => // E _.
rewrite subset0 => ->.
by rewrite s_measure0.
Qed.

Lemma sum_fine (R : numDomainType) (I : eqType) s (P : pred I) (F : I -> \bar R) :
  (forall i, (i \in s) || P i -> F i \is a fin_num) ->
  (\sum_(i <- s | P i) fine (F i) = fine (\sum_(i <- s | P i) F i))%R.
Proof.
move=> h; apply: EFin_inj; rewrite -sumEFin fineK; last first.
  by apply/sum_fin_numP => i si Pi; rewrite h// si.
by apply eq_bigr => i Pi; rewrite fineK ?h ?Pi ?orbT.
Qed.

Section hahn_decomposition_lemma.
Variables (d : _) (X : measurableType d) (R : realType).
Variables (mu : {smeasure set X -> \bar R}).

Let AA := @measurable _ X.

Lemma prop57 D : AA D -> mu D <= 0 ->
  {A | [/\ A `<=` D, negative_set mu A & mu A <= mu D] }.
Proof.
move=> AAD muD0.
pose seq_type (A : set X * \bar R * set X) :=
  measurable A.1.1 /\
  0 <= mu A.1.1 /\
  0 <= A.1.2 /\
  A.1.1 `<=` D /\
  mu A.1.1 >= mine (A.1.2 * 2^-1%:E) 1.
pose P (A1 A2 : {A : set X * \bar R * set X | seq_type A}) :=
  (proj1_sig A2).1.2 = ereal_sup
    [set mE | exists E, [/\ mE = mu E, measurable E & E `<=` D `\` (proj1_sig A1).2] ] /\
  (proj1_sig A2).1.1 `<=` D `\` (proj1_sig A1).2 /\
  (proj1_sig A2).2 = (proj1_sig A1).2 `|` (proj1_sig A2).1.1.
pose d0 : \bar R := ereal_sup [set mE | exists E, [/\ mE = mu E, measurable E & E `<=` D] ].
have d0_ge0 : 0 <= d0.
  by apply: ereal_sup_ub => /=; exists set0; split => //; rewrite s_measure0.
have [A0 [mA0 A0d0 A0D muA0_ge0]] :
    {A0 | [/\ measurable A0, mu A0 >= mine (d0 * 2^-1%R%:E) 1%E, A0 `<=` D & mu A0 >= 0] }.
  pose m0 := mine (d0 * 2^-1%R%:E) 1%E.
  apply/cid.
  move: d0_ge0; rewrite le_eqVlt => /orP[/eqP <-|d0_ge0].
    exists set0; split => //.
    rewrite mul0e.
    by rewrite min_l// s_measure0.
    by rewrite s_measure0.
  have m0_gt0 : 0 < m0.
    by rewrite /m0 lt_minr lte01 andbT mule_gt0//.
  have m0d0 : m0 < d0.
    rewrite /m0.
    have [->|d0oo] := eqVneq d0 +oo.
      by rewrite min_r// ?ltey// gt0_mulye// leey.
    rewrite -(@fineK _ d0); last first.
      by rewrite ge0_fin_numE// ?(ltW d0_ge0)// lt_neqAle d0oo leey.
    rewrite -EFinM minEFin lte_fin lt_minl.
    apply/orP; left.
    rewrite ltr_pdivr_mulr// ltr_pmulr// ?ltr1n// fine_gt0// d0_ge0/=.
    by rewrite lt_neqAle d0oo/= leey.
  move: (m0d0).
  move=> /ereal_sup_gt/cid2[x/= /cid[A0 [->{x} mA0 A0D m0muA0]]].
  exists A0; split => //.
  exact/ltW.
  by rewrite (le_trans _ (ltW m0muA0))// ltW.
pose U0 : set X := set0.
have : {AdU : nat -> {A : set X * \bar R * set X | seq_type A} |
  AdU 0%N = (exist _ (A0, d0, A0) (conj mA0 (conj muA0_ge0 (conj d0_ge0 (conj A0D A0d0))))) /\
  forall n, P (AdU n) (AdU n.+1)}.
  apply dependent_choice_Type => -[[[An dn] Un] [/= mAn mAn_ge0]].
  pose dn1 := ereal_sup [set mE | exists E, [/\ mE = mu E, measurable E & E `<=` D `\` Un] ].
  have dn1_ge0 : 0 <= dn1.
    by apply: ereal_sup_ub => /=; exists set0; split => //; rewrite s_measure0.
  have [An1 [mAn1 An1d1 An1UN muAn1_ge0] ] : {An1 | [/\ measurable An1,
                              mu An1 >= mine (dn1 * 2^-1%:E) 1,
                              An1 `<=` D `\` Un &
                              mu An1 >= 0] }.
    pose mn1 := mine (dn1 * 2^-1%R%:E) 1%E.
    apply/cid.
    move: dn1_ge0; rewrite le_eqVlt => /orP[/eqP <-|dn1_gt0].
      exists set0; split => //.
      rewrite mul0e.
      by rewrite min_l// s_measure0.
      by rewrite s_measure0.
    have mn1_gt0 : 0 < mn1.
      by rewrite /mn1 lt_minr lte01 andbT mule_gt0//.
    have : mn1 < dn1.
      rewrite /mn1.
      have [->|dn1oo] := eqVneq dn1 +oo.
        by rewrite min_r// ?ltey// gt0_mulye// leey.
      rewrite -(@fineK _ dn1); last first.
        by rewrite ge0_fin_numE// ?(ltW dn1_gt0)// lt_neqAle dn1oo leey.
      rewrite -EFinM minEFin lte_fin lt_minl.
      apply/orP; left.
      rewrite ltr_pdivr_mulr// ltr_pmulr// ?ltr1n// fine_gt0// dn1_gt0/=.
      by rewrite lt_neqAle dn1oo/= leey.
    move=> /ereal_sup_gt/cid2[x/= /cid[An1 [xE mAn1 An1DUn mn1x]]].
    exists An1; split.
    exact: mAn1.
    by rewrite -xE (le_trans _ (ltW mn1x))// /mn1.
    done.
    rewrite -xE (le_trans _ (ltW mn1x))// /mn1.
    by rewrite -/mn1 ltW.
  have An1D : An1 `<=` D.
    apply: (subset_trans An1UN).
    by apply: subDsetl.
  exists (exist _ (An1, dn1, Un `|` An1) (conj mAn1 (conj muAn1_ge0 (conj dn1_ge0 (conj An1D An1d1))))).
  split => /=.
  - done.
  - split => //.
move=> [AdU [AdU0 AdUn]].
set Aoo := \bigcup_k (proj1_sig (AdU k)).1.1.
have mAoo : measurable Aoo.
  apply bigcup_measurable => k _ /=.
  by case: (AdU k) => -[[? ?] ? []].
set B := D `\` Aoo.
have Ubig n : (proj1_sig (AdU n)).2 = \big[setU/set0]_(i < n.+1) (proj1_sig (AdU i)).1.1.
  elim: n => [|n ih]; rewrite /sval/=.
    by rewrite AdU0/= big_ord_recr/= big_ord0 set0U AdU0.
  rewrite /sval/= in ih.
  have [_ [_ ->]] := AdUn n.
  by rewrite big_ord_recr/= -ih.
have tA : trivIset [set: nat]
  (fun n : nat => ((@sval) (set X * \bar R * set X) [eta seq_type] (AdU n)).1.1).
  apply: subsetC_trivIset; rewrite /sval/= => n.
  have [_ [K1 _]] := AdUn n.
  apply (subset_trans K1).
  rewrite -setTD.
  apply: setDSS => //.
  rewrite Ubig.
  by rewrite big_ord_recr/=.
exists B.
have mA : (forall k : nat, d.-measurable ((@sval) (set X * \bar R * set X) [eta seq_type] (AdU k)).1.1).
  move=> k; rewrite /sval/=.
  by case: (AdU k) => -[[? ?] ?] [].
have cvg_muA : (fun n : nat =>
   \sum_(0 <= i < n)
      mu
        ((@sval) (set X * \bar R * set X) [eta seq_type]
           (AdU i)).1.1) --> mu Aoo.
  exact: (@smeasure_semi_sigma_additive _ _ _ mu (fun n => (proj1_sig (AdU n)).1.1) mA tA mAoo).
have muUA : mu Aoo >= 0.
  move/cvg_lim : cvg_muA => <-//=; apply: nneseries_ge0 => n _.
  by case: (AdU n) => -[[? ?] ?] [? []].
have A_cvg_0 :  (fun n => mu (proj1_sig (AdU n)).1.1) --> 0.
  rewrite [X in X --> _](_ : _ = EFin \o (fun n => fine (mu (proj1_sig (AdU n)).1.1))); last first.
    apply/funext => n/=.
    by rewrite fineK// isfinite//=.
  apply: continuous_cvg => //.
  apply/(@cvg_series_cvg_0 _ [normedModType R of R^o]).
  move: cvg_muA.
  rewrite -(@fineK _ (mu Aoo)) ?isfinite//.
  move/ereal_cvg_real => [H1 H2].
  rewrite (_ : series _ = fine \o (fun n : nat =>
     \sum_(0 <= i < n)
        mu
          ((@sval) (set X * \bar R * set X) [eta seq_type]
             (AdU i)).1.1)); last first.
    apply/funext => n /=.
    rewrite /series/= sum_fine//= => i _.
    rewrite isfinite//.
  apply/cvg_ex.
  by exists (fine (mu Aoo)).
have mine_cvg_0 : (fun n => mine ((proj1_sig (AdU n)).1.2 * (2^-1)%:E) 1) --> 0.
  apply: (@ereal_squeeze _ (cst 0) _ (fun n => mu (proj1_sig (AdU n)).1.1)); [|exact: cvg_cst|by []].
  apply: nearW => n /=.
  case: (AdU n) => [[[A_ d_] _] [/= _ [mu_ge0 [d_ge0 [_ ->]]]]].
  by rewrite andbT le_minr lee01 andbT mule_ge0.

have dn0 : (fun n => ((@sval) (set X * \bar R * set X) [eta seq_type] (AdU n)).1.2) --> 0.
  have : exists (N : nat), forall n, (n > N)%nat -> mine ((proj1_sig (AdU n)).1.2 * (2^-1)%:E) 1 =
                       ((proj1_sig (AdU n)).1.2 * (2^-1)%:E).
Admitted.


have EUn :forall n, E `<=` D `\` ((@sval) (set X * \bar R * set X) [eta seq_type] (AdU n)).2.
  move=> n.
  apply (subset_trans EB).
  rewrite /B.
  apply setDSS => //.
  rewrite /Aoo.
  rewrite Ubig.
  rewrite /sval.
  admit.
have Edn: forall n, mu E <= ((@sval) (set X * \bar R * set X) [eta seq_type] (AdU n)).1.2.
  elim.
    rewrite /sval.
    rewrite AdU0 //=.
    rewrite /d0.
    rewrite -(ereal_sup1 (mu E)).
    apply le_ereal_sup.
    move=> muE//= H.
    exists E.
    split=> //.
    apply (subset_trans EB).
    rewrite /B.
    apply subDsetl.
  move=> n Hn.
  admit.

Admitted.

End hahn_decomposition_lemma.

Lemma Hahn_decomposition_lemma d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
  let negatives := [set Z | negative_set nu Z] in
  let measure_negatives := [set nu Z | Z in negatives] in
  let alpha := ereal_inf measure_negatives in
  { N : (set X) ^nat |
  [/\ (forall i, negatives (N i)),
     (fun i => nu (N i)) --> alpha &
     alpha <= 0]}.
Proof.
move=> negatives.
move=> measure_negatives.
move=> alpha.
pose seq_type (A : set X * \bar R * set X) :=
  measurable A.1.1 /\
  nu A.1.1 <= 0.
pose P (A1 A2 : {A : set X * \bar R * set X | seq_type A}) :=
  (proj1_sig A2).1.2 = ereal_inf [set mE | exists E, [/\ mE = nu E, measurable E & E `<=` setT `\` (proj1_sig A1).2] ].
pose s0 : \bar R := ereal_inf [set mE | exists E, [/\ mE = nu E, measurable E & E `<=` setT] ].
have s0_le0 : s0 <= 0.
  by apply: ereal_inf_lb => /=; exists set0; split => //; rewrite s_measure0.
have [A0 [mA0 A0d0 muA0_le0]] :
    {A0 | [/\ measurable A0, nu A0 <= maxe (s0 * 2^-1%R%:E) (- 1%E) & nu A0 <= 0] }.
  pose m0 := maxe (s0 * 2^-1%R%:E) (- 1%E).
  have : s0 < m0.
    rewrite /m0.
    admit.
  move=> /ereal_inf_lt/cid2[x/= /cid[A0 [->{x} mA0 A0D m0muA0]]].
  exists A0; split => //.
  exact/ltW.
  admit.
pose U0 : set X := set0.
have : {AdU : nat -> {A : set X * \bar R * set X | seq_type A} |
  AdU 0%N = (exist _ (A0, s0, setT) (conj mA0 muA0_le0)) /\
  forall n, P (AdU n) (AdU n.+1)}.
  apply dependent_choice_Type => -[[[An dn] Un] [/= mAn nuAn_le0]].
  pose sn1 := ereal_inf [set mE : \bar R | exists E, [/\ mE = nu E, measurable E & E `<=` setT `\` Un] ].
  have sn1_le0 : sn1 <= 0.
    admit.
  have [An1 [mAn1 An1d1 muAn1_ge0] ] : {An1 | [/\ measurable An1,
                              nu An1 <= maxe (s0 * 2^-1%:E) (- 1%E)%E &
                              nu An1 <= 0] }.
    pose mn1 := maxe (sn1 * 2^-1%R%:E) (- 1%E).
    have [Nn [NnAn negativeNn nuNnAn]] := prop57 mAn nuAn_le0.
    have : sn1 < mn1.
      rewrite /mn1.
      admit.
    move=> /ereal_inf_lt/cid2[x/= /cid[An1 [xE mAn1 An1DUn mn1x]]].
    exists An1; split.
    exact: mAn1.
    rewrite -xE (le_trans (ltW mn1x))// /mn1.
    admit.
    rewrite -xE (le_trans (ltW mn1x))// /mn1.
    admit.
  exists (exist _ (An1, sn1, setT `\` An `|` An1) (conj mAn1 muAn1_ge0)).
  split => /=.
move=> [AdU [AdU0 AdUn]].
exists (fun n => (proj1_sig (AdU n)).1.1).
split => //.
- move=> n.
  admit.
- admit.
- admit.
Admitted.

Lemma lte_naddl {R : realDomainType} (x : \bar R) [y : \bar R] :
  x \is a fin_num -> y < 0 -> x + y < x.
Proof.
move=> xf x0.
by rewrite -lte_suber_addr// lte_addl// lte_oppr oppe0.
Qed.

Lemma bigcup_negative_set d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) (N_ : (set X)^nat) :
  (forall i, negative_set nu (N_ i)) ->
  negative_set nu (\bigcup_i N_ i).
Proof.
move=> H.
have mN : measurable (\bigcup_i N_ i).
  apply: bigcup_measurable => n _.
  by have [/[1!inE]] := H n.
split=> [/[1!inE]//| S /[1!inE] mS SN].
pose S_ m := (S `&` N_ m) `\` \bigcup_(j in `I_m) N_ j.
have S_E : S_ = seqDU (fun n => S `&` N_ n).
  apply/funext => m; rewrite /S_ -setIDA.
  (* TODO: lemma *) apply/seteqP; split.
    (* NB: lemma? *)
    move=> x [Sx [Nmx Nx]]; split=> //.
    apply: contra_not Nx => /=.
    rewrite bigcup_mkord.
    by rewrite -big_distrr/= => -[].
  rewrite /seqDU -setIDA bigcup_mkord -big_distrr/=.
  by rewrite setDIr setIUr setDIK set0U.
have tS_ : trivIset setT S_.
  by rewrite S_E; exact: trivIset_seqDU.
have SN_ m : S_ m `<=` N_ m by move=> x [[]].
have SS_ : S = \bigcup_i S_ i.
  transitivity (\bigcup_i seqDU (fun n : nat => S `&` N_ n) i); last first.
    by apply: eq_bigcup => // n _; rewrite S_E.
  by rewrite -seqDU_bigcup_eq -setI_bigcupr setIidl.
have ? : forall n, measurable (S_ n).
  move=> n; rewrite /S_; apply: measurableD.
    apply: measurableI => //.
    by have [/[1!inE]] := H n.
  apply: bigcup_measurable => // k _.
  by have [/[1!inE]] := H k.
have S_S : (fun n => \sum_(0 <= i < n) nu (S_ i)) --> nu S.
  rewrite SS_; apply: smeasure_semi_sigma_additive => //.
  exact: bigcup_measurable.
have nuS_ m : nu (S_ m) <= 0.
  have [_] := H m.
  by apply => //; first by rewrite inE.
rewrite (_ : nu S = lim (fun n => \sum_(0 <= i < n) (nu (S_ i)))); last first.
  exact/esym/cvg_lim.
apply: ereal_lim_le.
  apply/cvg_ex => /=; first eexists; exact: S_S.
by apply: nearW => n; exact: sume_le0.
Qed.

Lemma negative_setU d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) N M :
  negative_set nu N -> negative_set nu M -> negative_set nu (N `|` M).
Proof.
move=> nN nM.
rewrite -bigcup2E.
apply: bigcup_negative_set => -[//|[//|/= _]].
exact: negative_set0.
Qed.

Theorem Hahn_decomposition d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
  exists P N,
   [/\ positive_set nu P,
      negative_set nu N,
      P `|` N = setT &
      P `&` N = set0].
Proof.
pose negatives := [set Z | negative_set nu Z].
have negatives_nonempty : negatives !=set0.
  by exists set0; apply: negative_set0.
pose measure_negatives := [set nu Z | Z in negatives].
pose alpha := ereal_inf measure_negatives. (* ereal_inf_EFin *)
have [N_ [negN_ cvgN_ alpha0]]: {N : (set X) ^nat |
  [/\ (forall i, negatives (N i)),
     (fun i => nu (N i)) --> alpha &
     alpha <= 0]}.
  exact: Hahn_decomposition_lemma.
pose N := \bigcup_i (N_ i).
have mN : measurable N.
  apply: bigcup_measurable => n _.
  by have [/[1!inE]] := negN_ n.
have negative_set_N : negative_set nu N.
  apply: bigcup_negative_set => i.
  by have [] := negN_ i.
have nuN_alpha : nu N = alpha.
  have H1 m : nu (N `\` N_ m) <= 0.
    apply negative_set_N.2.
      rewrite inE; apply: measurableD => //.
      by have [/[1!inE]] := negN_ m.
      exact: subDsetl.
  have {H1}H2 m : nu N <= nu (N_ m).
    rewrite -(@setDUK _ (N_ m) N); last exact: bigcup_sup.
    rewrite s_measureU//; last 3 first.
      by have [/[1!inE]] := negN_ m.
      apply: measurableD => //.
      by have [/[1!inE]] := negN_ m.
      by rewrite setDIK.
      by rewrite gee_addl.
  have {H2}H3 : nu N <= alpha.
    rewrite [leRHS](_ : _ = lim (nu \o N_)); last exact/esym/cvg_lim.
    apply: ereal_lim_ge.
      by apply/cvg_ex => /=; first eexists; exact: cvgN_.
    exact: nearW.
  apply/eqP; rewrite eq_le H3 /=.
  by apply: ereal_inf_lb; exists N.
have alphay : alpha > -oo by rewrite -nuN_alpha ltNye_eq isfinite.
pose P := setT `\` N.
have mP : measurable P.
apply measurableD => //.
have positive_P : positive_set nu P.
  rewrite /positive_set inE.
  split=> [//|] E mE EP.
  rewrite (_ : nu E = s_mrestr nu mP E); last by rewrite /s_mrestr setIidl.
  move: E mE EP.
  apply: positive_set_0' => //.
  move=> N' mN' negativeN'.
  apply /eqP.
  rewrite eq_le.
  rewrite -(negbK (_&&_)).
  rewrite (negative_set_smeasure0 negativeN') /=.
  rewrite -ltNge.
  apply/negP.
  move=> N'0.
  pose UNN' := N `|` (N' `&` P).
  have mUNN' : measurable UNN'.
    apply: measurableU => //.
    by apply: measurableI => //.
  have : nu UNN' < alpha.
    rewrite s_measureU //; last 2 first.
      by have [/[1!inE]] := negativeN'.
      have N'N : (N' `&` P) `<=` ~` N.
        have N'P : N' `&` P `<=` P.
          exact: subIsetr.
        by rewrite -setTD.
      by rewrite setIC; apply/disjoints_subset.
    by rewrite -nuN_alpha lte_naddl// isfinite//.
  rewrite ltNge => /negP; apply.
  have ? : negative_set nu UNN' by exact: negative_setU.
  by apply: ereal_inf_lb; exists UNN'.
exists P, N; split => //.
by rewrite /P setTD setvU.
by rewrite /P setTD setvI.
Qed.

Definition is_Hahn_decomposition d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :=
  fun P N =>
   [/\ positive_set nu P,
      negative_set nu N,
      P `|` N = setT &
      P `&` N = set0].

Lemma positive_negative0  d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
    forall P N, positive_set nu P -> negative_set nu N ->
            forall S, measurable S -> nu (S `&` P `&` N) = 0.
Proof.
move=> P N [mP posP] [mN negN] S mS.
rewrite !inE in mP mN mS.
apply /eqP.
rewrite eq_le.
apply /andP; split.
  apply negN.
    rewrite inE.
    apply measurableI => //; apply: measurableI => //.
  apply setIidPl.
  by rewrite -setIA setIid.
rewrite -setIAC.
apply posP.
  rewrite inE.
  apply measurableI => //; apply measurableI => //.
apply setIidPl.
by rewrite -setIA setIid.
Qed.

Lemma s_measure_partition2 d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
    forall P N, measurable P -> measurable N -> P `|` N = setT -> P `&` N = set0 ->
      forall S, measurable S -> nu S = nu (S `&` P) + nu (S `&` N).
Proof.
move=> P N mP mN PNT PN0 S mS.
rewrite -{1}(setIT S) -PNT setIUr s_measureU//.
  1,2:by apply measurableI.
by rewrite setICA -(setIA S P N) PN0 setIA setI0.
Qed.

(* memo : trying to auto resolve a following lemma but it doesn't work *)
(*
Lemma positive_set_is_measurable d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
      forall P, positive_set nu P -> measurable P.
Proof.
move=> P [mP _].
by rewrite inE in mP.
Qed.

Hint Resolve positive_set_is_measurable.
*)

Lemma Hahn_decomposition_measure_uniqueness
  d (X : measurableType d) (R : realType)
    (nu : {smeasure set X -> \bar R}) :
  forall P1 N1 P2 N2,
   is_Hahn_decomposition nu P1 N1 -> is_Hahn_decomposition nu P2 N2 ->
   forall S, measurable S ->
          nu (S `&` P1) = nu (S `&` P2) /\ nu (S `&` N1) = nu (S `&` N2).
Proof.
move=> P1 N1 P2 N2 Hahn1 Hahn2 S mS.
move: (Hahn1) (Hahn2) => [posP1 negN1 PN1T PN10] [posP2 negN2 PN2T PN20].
move: (posP1) (negN1) (posP2) (negN2) => [mP1 _] [mN1 _] [mP2 _] [mN2 _].
rewrite !inE in mP1 mN1 mP2 mN2.
have mSP1 := (measurableI S P1 mS mP1).
have mSN1 := (measurableI S N1 mS mN1).
have mSP2 := (measurableI S P2 mS mP2).
have mSN2 := (measurableI S N2 mS mN2).
split.
  apply (@eq_trans _ _ (nu (S `&` P1 `&` P2))).
     by rewrite (s_measure_partition2 nu mP2 mN2 PN2T PN20)//
       (positive_negative0 posP1 negN2 mS) adde0.
   by rewrite [RHS](s_measure_partition2 nu mP1 mN1 PN1T PN10)//
     (positive_negative0 posP2 negN1 mS) adde0 setIAC.
apply (@eq_trans _ _ (nu (S `&` N1 `&` N2))).
   by rewrite (s_measure_partition2 nu mP2 mN2 PN2T PN20)//
     {1}setIAC (positive_negative0 posP2 negN1 mS) add0e.
 by rewrite [RHS](s_measure_partition2 nu mP1 mN1 PN1T PN10)//
   (setIAC _ _ P1) (positive_negative0 posP1 negN2 mS) add0e setIAC.
Qed.

(* Definition  : measureable -> R :=  *)

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
 *   forall x, 0 <= g m x, g m in G
 *)
 (* max_g2' : (T -> R)^nat :=
  fun k t => (\big[maxr/0]_(i < k) (g2' i k) t)%R. *)
pose E m j := [set x | F m x = g j x /\ forall k, (k < j)%nat -> F m x > g k x ].
have measurable_E m j : E m j \in measurable.
  admit.
have partition_E m : partition setT (E m) setT.
  admit.
(* Local Open Scope ereal_scope. *)
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
Proof.
Abort.

Theorem FTC2 d (R : realType) (f : R -> R) (a b : R)
     (f_abscont : abs_continuous_function f (a, b) )
       : exists f' : R -> \bar R, summable `[a, b] f' /\
         {ae (@lebesgue_measure d R), forall x, x \in `[a, b] ->f' x \is a fin_num}
           /\ forall x, x \in `[a, b] ->
             (f x - f a)%:E = (integral (@lebesgue_measure d R) `[a ,x] f').
Proof.
Abort.
