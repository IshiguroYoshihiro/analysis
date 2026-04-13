From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_ssreflect interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import mathcomp_extra boolp contra classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure numfun realfun.
From mathcomp Require Import absolute_continuity.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 4)                                         *)
(*                                                                            *)
(*   cplt_hull P            == A relative complement of P in convex hull of P.*)
(*   contiguous_intervals P == A countable family of component intervals of   *)
(*                             cplt_hull P, called as "intervals contiguous   *)
(*                             to P" in Ene's Proof.                          *)
(* ref: https://projecteuclid1.org/journals/real-analysis-exchange/volume-23/ *)
(*issue-1/An-Elementary-Proof-of-the-Banach-Zarecki-Theorem/rae/              *)
(*1337086099.full*)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma image_bigcup_disjoint T U (f : T -> U) I (D : set I)
   (F : I -> set T) :
  trivIset D F -> f @` (\bigcup_(i in D) F i) = \bigcup_(i in D) f @` F i.
Proof.
move=> DS.
apply/seteqP; split => [_ [x [i Di Six <-]]|_ [i Di [x Six <-]]].
  by exists i.
by exists x => //; exists i.
Qed.

Section cplt_hull.
Context {R : realType}.
Implicit Type (A : set R).

(* complement hull? *)
Definition cplt_hull A := [set` Rhull A] `\` A.

Lemma cplt_hull0 A : is_interval A -> cplt_hull A = set0.
Proof.
by move=> itvA; rewrite /cplt_hull -((is_intervalP A).1 itvA) setDv.
Qed.

Lemma cplt_hull_set0 : cplt_hull set0 = set0.
Proof. by rewrite cplt_hull0. Qed.

Lemma cplt_hullT : cplt_hull setT = set0.
Proof. by rewrite cplt_hull0. Qed.

Lemma cplt_hull_subset_Rhull A : cplt_hull A `<=` [set` Rhull A].
Proof. exact: subDsetl. Qed.

(* NB: PR in progress *)
Lemma not_nonemptyP A : ~ (A !=set0) <-> A = set0.
Proof. by split; [|move=> ->]; move/set0P/negP; [move/negbNE/eqP|]. Qed.

Lemma has_ubound_cplt_hull A :
  has_ubound A -> has_ubound (cplt_hull A).
Proof.
move=> /[dup]/asboolP u [ub ubAub]; exists ub => x [+ _].
have [|/=/contrapT A0] := pselect (~ (A !=set0)).
  by move/not_nonemptyP ->; rewrite RhullK ?inE.
by rewrite in_itv/= u => /andP[_]/lteifW/le_trans; apply; exact: ge_sup.
Qed.

Lemma has_lbound_cplt_hull A :
  has_lbound A -> has_lbound (cplt_hull A).
Proof.
move=> /[dup]/asboolP l [lb lbAlb]; exists lb => x [+ _].
have [/= A0|] := pselect (A !=set0); last first.
  by move/set0P/negP/negbNE/eqP => ->; rewrite Rhull0 set_itvoo0.
rewrite in_itv/= l => /andP[+ _] => /lteifW; apply: le_trans; exact: lb_le_inf.
Qed.

Lemma cplt_hull_complement A : cplt_hull A `<=` ~` A.
Proof. rewrite /cplt_hull; exact: subDsetr. Qed.

(* unused *)
Lemma cplt_hull_sup A : has_ubound A -> ~ (cplt_hull A) (sup A).
Proof.
move=> ubA; rewrite /cplt_hull/= in_itv/= andC -implypN => Asup.
by move/asboolPn: (Asup); move/asboolP: (ubA) => -> -> /=; rewrite ltxx andbF.
Qed.

(* notable property of cplt_hull *)
(*
Lemma rray_has_ubound_cplt_hull A :
  A \in (nbhs +oo) -> has_ubound (cplt_hull A).
Proof.
rewrite inE.
move=> [b [_ Hb]].
Abort.
*)

Lemma cplt_hull_lt_sup A :
  has_ubound A -> cplt_hull A `<=` [set x | x < sup A].
Proof.
move=> hasubA x [/= + nAx].
rewrite in_itv/=; move/andP => [_]; rewrite ifT; last by exact/asboolP.
have [/asboolP/= ?|//] := boolP `[< A (sup A)>];
by rewrite le_eqVlt => /predU1P[|//]=> ?; subst.
Qed.

(* unused *)
Lemma cplt_hull_inf A :
  has_lbound A -> ~ (cplt_hull A) (inf A).
Proof.
move=> haslbA.
rewrite /cplt_hull/=.
apply/not_andP.
rewrite orpN => Ainf.
have gt_inf := inf_lb_strict haslbA Ainf.
rewrite in_itv/=.
case: ifP; move/asboolP => //= _.
move/asboolPn/negPf : Ainf => -> /=.
by rewrite ltxx.
Qed.

Lemma inf_lt_cplt_hull A :
  has_lbound A -> cplt_hull A `<=` [set x | inf A < x].
Proof.
move=> haslbA x [/= + nAx].
rewrite in_itv/=.
move/andP => [+ _]; move/asboolP : (haslbA) => ->.
have [|/asboolF -> //] := pselect (A (inf A)).
move=> /[dup]/asboolP -> AinfA/=.
rewrite le_eqVlt => /orP[|//]; move/eqP => xinfA.
by move: nAx; rewrite -xinfA.
Qed.

Lemma cplt_hullEitvoo A :
  has_ubound A -> has_lbound A ->
  cplt_hull A = `]inf A, sup A[ `&` ~` A.
Proof.
move/[dup]/cplt_hull_lt_sup => ciAsup hasubA.
move/[dup]/inf_lt_cplt_hull => ciAinf haslbA.
rewrite eqEsubset; split.
- move=> x ciA/=; split.
  + rewrite in_itv/=; apply/andP; split.
    * exact: ciAinf.
    * exact: ciAsup.
  + by move: ciA; rewrite /cplt_hull/= => -[].
rewrite /cplt_hull setDE; apply: setSI.
rewrite/Rhull.
move: hasubA haslbA => /asboolP -> /asboolP ->.
case: `[< A (inf A) >]; case: `[< A (sup A) >] => //=.
- exact: subset_itv_oo_cc.
- exact: subset_itv_oo_co.
- exact: subset_itv_oo_oc.
Qed.

Lemma cplt_hullEitvyo A :
  has_ubound A -> ~ has_lbound A ->
  cplt_hull A = `]-oo, sup A[ `&` ~` A.
Proof.
move/[dup]/cplt_hull_lt_sup => ciAsup hasubA.
move=> hasNlbA.
rewrite /cplt_hull.
rewrite /Rhull.
move/asboolP : (hasubA) => ->.
move/asboolF : (hasNlbA) => -> /=.
have [Asup|nAsup] := pselect (A (sup A)).
  move/asboolP : (Asup) => ->/=.
  rewrite -(setUitv1 true)// setDUl -[RHS]setU0; congr setU.
  rewrite setD_eq0.
  by rewrite sub1set inE.
by move/asboolF : nAsup => ->.
Qed.

Lemma cplt_hullEitvoy A :
  ~ has_ubound A -> has_lbound A ->
  cplt_hull A = `]inf A, +oo[ `&` ~` A.
Proof.
move=> hasNubA.
move/[dup]/inf_lt_cplt_hull => ciAinf haslbA.
rewrite /cplt_hull.
rewrite /Rhull.
move/asboolP : (haslbA) => ->.
move/asboolF : (hasNubA) => -> /=.
have [Ainf|nAinf] := pselect (A (inf A)).
  move/asboolP : (Ainf) => ->/=.
  rewrite -(setU1itv false)// setDUl -[RHS]set0U; congr setU.
  rewrite setD_eq0.
  by rewrite sub1set inE.
by move/asboolF : nAinf => ->.
Qed.

Lemma cplt_hull_unboundEitvoo A :
  A !=set0 -> ~ has_ubound A -> ~ has_lbound A ->
  cplt_hull A = ~` A.
Proof.
move=> [x Ax].
move=> hasNubA hasNlbA.
rewrite -setTD; congr setD.
rewrite/Rhull.
move/asboolF : hasNlbA => ->.
move/asboolF : hasNubA => ->.
exact: interval_unbounded_setT.
Qed.

Let compact_open_complement A : compact A -> open (cplt_hull A).
Proof.
move=> cpA.
have := compact_bounded cpA.
move=> -[bnd [_ bndA]].
rewrite cplt_hullEitvoo; last 2 first.
- exists (bnd + 1) => x Ax.
  rewrite ler_normlW//.
  apply: bndA => //.
  by rewrite ltrDl.
- exists (- (bnd + 1)) => x Ax.
  rewrite lerNnormlW//.
  apply: bndA => //.
  by rewrite ltrDl.
apply: openI => //.
apply: closed_openC.
exact: (compact_closed _ cpA).
Qed.

Lemma closed_open_cplt_hull A : closed A -> open (cplt_hull A).
Proof.
move=> cA.
have [ubA|ubA] := pselect (has_ubound A).
- have [lbA|lbA] := pselect (has_lbound A).
  + rewrite cplt_hullEitvoo//.
    by apply: openI => //; rewrite openC.
  + rewrite cplt_hullEitvyo//.
    by apply: openI => //; rewrite openC.
- have [lbA|lbA] := pselect (has_lbound A).
  + rewrite cplt_hullEitvoy//.
    by apply: openI => //; rewrite openC.
  + have [A0|/set0P/negP/negPn/eqP ->] := pselect (A !=set0).
      by rewrite cplt_hull_unboundEitvoo// openC.
    by rewrite cplt_hull_set0.
Qed.

End cplt_hull.

(* TODO *)
Definition cont_itv1 {R : realType} (A : set R) (s_ : R^nat) :=
  fun k => Num.min (sup A) (s_ k.-1).

Definition cont_itv2 {R : realType} (A : set R) (i_ : R^nat) :=
  fun k => Num.max (i_ k) (inf A).

Definition cont_itvs {R : realType} (A : set R) (i_ s_ : R^nat) : (set R)^nat :=
  fun k => [set` `[cont_itv1 A s_ k, cont_itv2 A i_ k]].

Section cont_itvs.
Context {R : realType}.
Variables A : set R.

Lemma cont_itvsS i_ s_ k :
  (forall k, i_ k \in `[inf A, sup A]) ->
  (forall k, s_ k \in `[inf A, sup A]) ->
  cont_itvs A i_ s_ k `<=` `[inf A, sup A].
Proof.
move=> icd scd r.
rewrite /cont_itvs /cont_itv1 /cont_itv2/=.
rewrite !in_itv/= => /andP[H1 H2].
apply/andP; split.
Abort.

End cont_itvs.

(* NB: A is supposed to be a perfect set so that A is closed *)
Definition contiguous_intervals {R : realType} (A : set R) : (set R)^nat :=
  match pselect (closed A) with
  | left H => open_disjoint_itv (closed_open_cplt_hull H)
  | right _ => cst set0
  end.

Definition contiguous_intervals1 {R : realType} (A : set R) : R^nat :=
  fun n => inf (contiguous_intervals A n).

Definition contiguous_intervals2 {R : realType} (A : set R) : R^nat :=
  fun n => sup (contiguous_intervals A n).

Lemma is_subset1_set1 {R : realType} (A : set R) : A !=set0 -> is_subset1 A ->
  A = [set xget point A].
Proof.
move=> A0 A1.
case: xgetP => /= [_ -> Aget|].
  apply/seteqP; split => [x Ax/=|x/= ->//].
  exact: A1.
by case: A0 => s As /(_ s).
Qed.

(* TODO: move near has_bound_not_subset1_inf_sup in absolute_continuity.v *)
Lemma has_bound_inf_sup {R : realType} (A : set R) : A !=set0 ->
  has_lbound A -> has_ubound A -> (inf A <= sup A)%R.
Proof.
move=> A0 lbA ubA.
have [|/has_bound_not_subset1_inf_sup] := pselect (is_subset1 A); last first.
  by move=> /(_ lbA ubA) /ltW.
move/is_subset1_set1 => /(_ A0) ->.
by rewrite inf1 sup1.
Qed.

Section contiguous_intervals_lemmas.
Context {R : realType}.
Implicit Type (A : set R).

Lemma open_contiguous_intervals A n : open (contiguous_intervals A n).
Proof.
rewrite /contiguous_intervals; case: pselect => cA//.
exact: open_disjoint_itv_open.
Qed.

Lemma is_interval_contiguous_intervals A n :
  is_interval (contiguous_intervals A n).
Proof.
rewrite /contiguous_intervals; case: pselect => cA//.
exact: open_disjoint_itv_is_interval.
Qed.

Lemma disjoint_contiguous_intervals A :
  trivIset [set: nat] (contiguous_intervals A).
Proof.
rewrite /contiguous_intervals; case: pselect => cA//.
  exact: open_disjoint_itv_trivIset.
exact: trivIset_set0.
Qed.

Lemma bigcup_contiguous_intervals A :
  closed A -> cplt_hull A = \bigcup_k (contiguous_intervals A) k.
Proof.
move=> cA.
rewrite /contiguous_intervals; case: pselect => ? //.
by rewrite -open_disjoint_itv_bigcup.
Qed.

Lemma contiguous_intervals_subsetC A n :
  contiguous_intervals A n `<=` ~` A.
Proof.
rewrite /contiguous_intervals; case: pselect => cA//=.
apply: (@subset_trans _ (cplt_hull A)); last first.
  exact: cplt_hull_complement.
rewrite [in X in _ `<=` X](open_disjoint_itv_bigcup (closed_open_cplt_hull cA)).
exact: bigcup_sup.
Qed.

Lemma contiguous_intervalsS A n :
  contiguous_intervals A n `<=` cplt_hull A.
Proof.
have [cA|cA] := pselect (closed A).
  by rewrite (bigcup_contiguous_intervals cA); exact: bigcup_sup.
(* NB: needs lemma here *)
by rewrite /contiguous_intervals; case: pselect.
Qed.

Lemma has_lbound_contiguous_intervals A :
  has_lbound A -> forall n, has_lbound (contiguous_intervals A n).
Proof.
move/inf_lt_cplt_hull => lbA i; exists (inf A) => r.
by move/contiguous_intervalsS/lbA => /= /ltW.
Qed.

Lemma has_ubound_contiguous_intervals A :
  has_ubound A -> forall n, has_ubound (contiguous_intervals A n).
Proof.
move/cplt_hull_lt_sup => lbA i; exists (sup A) => r.
by move/contiguous_intervalsS/lbA => /= /ltW.
Qed.

(*Lemma contiguous_intervals1_fin_num A : has_lbound A ->
 forall n, contiguous_intervals1 A n \is a fin_num.
Proof.
move=> + i.
move/has_lbound_contiguous_intervals => /(_ i) lbA.
rewrite /contiguous_intervals1 /Rhull; case: ifPn => //=.
by move/asboolP.
Qed.

Lemma contiguous_intervals2_fin_num A : has_ubound A ->
 forall i, contiguous_intervals2 A i \is a fin_num.
Proof.
move=> + i.
move/has_ubound_contiguous_intervals => /(_ i) ubA.
rewrite /contiguous_intervals2 /Rhull; case: ifPn => /=; case: ifPn => //.
  by move/asboolP.
by move/asboolP.
Qed.*)

Lemma contiguous_intervals1_le_contiguous_intervals2 A n :
  has_lbound A ->
  has_ubound A ->
  (contiguous_intervals1 A n <= contiguous_intervals2 A n)%R.
Proof.
move=> ? ?.
rewrite /contiguous_intervals1 /contiguous_intervals2.
have [An0|] := pselect ((contiguous_intervals A n) !=set0); last first.
  move/set0P/negP/negPn/eqP ->.
  by rewrite inf0 sup0.
rewrite has_bound_inf_sup//.
  exact: has_lbound_contiguous_intervals.
exact: has_ubound_contiguous_intervals.
Qed.

Lemma bigcup_contiguous_intervals_fine A :
  compact A -> cplt_hull A =
      \bigcup_k `](contiguous_intervals1 A k),
                  (contiguous_intervals2 A k)[%classic.
Proof.
move=> cA.
have closedA : closed A by exact: compact_closed.
rewrite bigcup_contiguous_intervals//.
apply: eq_bigcupr => n _.
transitivity [set` Rhull (contiguous_intervals A n)].
  by rewrite RhullK//; rewrite inE; exact: is_interval_contiguous_intervals.
have haslbA : has_lbound A.
  apply: bounded_has_lbound.
  exact: compact_bounded.
have hasubA : has_ubound A.
  apply: bounded_has_ubound.
  exact: compact_bounded.
have [haslbciA hasubciA citvAinf citvAsup] :
  [/\ has_lbound (contiguous_intervals A n),
       has_ubound (contiguous_intervals A n),
       ~ contiguous_intervals A n (inf (contiguous_intervals A n))&
       ~ contiguous_intervals A n (sup (contiguous_intervals A n))].
  split.
  - exact: has_lbound_contiguous_intervals.
  - exact: has_ubound_contiguous_intervals.
  - apply: open_haslb_memNinf.
    + exact: has_lbound_contiguous_intervals.
    + exact: open_contiguous_intervals.
  - apply: open_hasub_memNsup.
    + exact: has_ubound_contiguous_intervals.
    + exact: open_contiguous_intervals.
rewrite /contiguous_intervals1/contiguous_intervals2/Rhull/=.
move/asboolP: haslbciA ->; move/asboolP: hasubciA ->.
by move/asboolF: citvAinf ->;move/asboolF: citvAsup ->.
Qed.

Lemma fine_contiguous_intervals1 A : (*compact A ->*)
  forall i, contiguous_intervals1 A i = inf (contiguous_intervals A i).
Proof. by []. Qed.

Lemma fine_contiguous_intervals2 A : (*compact A ->*)
  forall i, contiguous_intervals2 A i = sup (contiguous_intervals A i).
Proof. by []. Qed.

(* unused *)
Lemma contiguous_ooitv A :
  has_ubound A -> has_lbound A ->
  forall i, (contiguous_intervals A i) =
   `]contiguous_intervals1 A i, contiguous_intervals2 A i[%classic.
Proof.
move=> /[dup] hasubA [u Au] /[dup] haslbA [l Al] i.
rewrite /contiguous_intervals1/contiguous_intervals2.

rewrite -{1}(@RhullK _ (contiguous_intervals A i)); last first.
  by rewrite inE; exact: is_interval_contiguous_intervals.

rewrite /Rhull.
rewrite 2?ifT/=; last 2 first.
- exact/asboolP/has_ubound_contiguous_intervals.
- exact/asboolP/has_lbound_contiguous_intervals.
have : ~ contiguous_intervals A i(inf (contiguous_intervals A i)).
   apply: open_haslb_memNinf.
    exact: has_lbound_contiguous_intervals.
  exact: open_contiguous_intervals.
have : ~ contiguous_intervals A i (sup (contiguous_intervals A i)).
  apply: open_hasub_memNsup.
    exact: has_ubound_contiguous_intervals.
  exact: open_contiguous_intervals.
by move=> /asboolF -> /asboolF ->//=.
(* lemma? *)
(*rewrite eqEsubset; split.
  by move=> z [x/= + <-]; rewrite 2!in_itv/= 2!lte_fin.
move=> z/=; rewrite in_itv/= => /andP[infz zsup].
have finz : z \is a fin_num.
  rewrite fin_numElt; apply/andP; split.
  - by apply: lt_trans infz; rewrite ltNyr.
  - by apply: (lt_trans zsup); rewrite ltry.
move: infz zsup.
move/EFin_fin_numP : finz => [x ->]; rewrite 2!lte_fin => infx xsup.
by exists x => //; rewrite in_itv/= infx xsup.*)
Qed.

End contiguous_intervals_lemmas.

Section lemma4_preliminaries.
Context {R : realType}.

Lemma eq_Rhull_itvccP A (a b : R) :
  Rhull A = `[a, b] <->
  [/\ has_lbound A, A (inf A) & inf A = a] /\
  [/\ has_ubound A, A (sup A) & sup A = b].
Proof.
split.
- rewrite /Rhull.
  case: ifP => // /asboolP haslbA.
  case: ifP => // /asboolP hasubA.
  have [/[dup]infP /asboolP -> /= |/asboolF -> //] := pselect (A (inf A)).
  have [/[dup]supP /asboolP -> /= |/asboolF -> //] := pselect (A (sup A)).
  case => infPa supPb.
  by split; split.
- move=> [[haslbA Ainf infa] [hasubA Asup supa]].
  rewrite /Rhull.
  move/asboolP: haslbA ->; move/asboolP: hasubA ->.
  move/asboolP: Ainf ->; move/asboolP: Asup ->.
  by rewrite infa supa.
Qed.

Lemma interval_ooS (A : set R) : inf A <= sup A -> `](inf A), (sup A)[ `<=` [set` Rhull A].
Proof.
move=> infsup r/= rA.
rewrite /Rhull.
case: ifPn => // lA.
  case: ifPn => // uA.
    rewrite !in_itv/= negbK.
    have [Ainf|Ainf]/= := boolP (`[< A (inf A) >]);
      have [Asup|Asup]/= := boolP (`[< A (sup A) >]); by rewrite !(itvP rA).
  rewrite !in_itv/= andbT.
  have [Asup|Asup]/= := boolP (`[< A (inf A) >]); by rewrite !(itvP rA).
case: ifPn => // uA.
rewrite in_itv/= negbK.
have [Asup|Asup]/= := boolP (`[< A (sup A) >]); by rewrite !(itvP rA).
Qed.

Local Open Scope ereal_scope.

Lemma interval_ooS_old (A : interval R) : A.1 <= A.2 -> `](fine A.1), (fine A.2)[ `<=` [set` A].
Proof.
move: A => [r s].
move: r => [[|]r|[|]]; move: s => [[|]s|[|]]//= rs x/=; rewrite ?in_itv//=.
- by move=> /andP[/ltW -> ->].
- by move=> /andP[/ltW -> /ltW ->].
- by move=> /andP[/ltW ->].
- by move=> /andP[-> /ltW ->].
- by move=> /andP[->].
- by move=> /andP[_ ->].
- by move=> /andP[_ /ltW ->].
- by move=> /andP[] /lt_trans /[apply]; rewrite ltxx.
- by move=> /andP[] /lt_trans /[apply]; rewrite ltxx.
Qed.

Lemma Rull_fst_snd (A : set R) : (Rhull A).1 <= (Rhull A).2.
Proof.
have [->|A0] := eqVneq A set0; first by rewrite !Rhull0.
rewrite /Rhull; case: ifPn => /asboolP lA; case: ifPn => // /asboolP uA /=.
- by rewrite lee_fin has_bound_inf_sup//; exact/set0P.
- by rewrite leey.
- by rewrite leNye.
Qed.

(* TODO: PR *)
Lemma hasNlb_ereal_inf (A : set R) :
  ~ has_lbound A -> A !=set0 -> ereal_inf (EFin @` A) = -oo.
Proof.
move=> hasNlbA A0.
rewrite ereal_infEN.
rewrite [X in - ereal_sup X = _](_ : _ =
  (EFin @` (-%R @` A))); last first.
  rewrite eqEsubset; split.
  - move=> _ [_ [r Ar <-] <-].
    by exists (- r)%R.
  - move=> _ [_ [r Ar <-] <-].
    by exists r%:E.
rewrite hasNub_ereal_sup//.
- by rewrite -has_lb_ubN.
- exact: image_nonempty.
Qed.

Lemma trivIset_contiguous_intervals (P : set R) :
  has_lbound P -> has_ubound P ->
  let a_ := contiguous_intervals1 P : (R) ^nat in
  let b_ := contiguous_intervals2 P : (R) ^nat in
  trivIset [set: nat] (fun i : nat => `]((a_ i)), ((b_ i))[%classic).
Proof.
move=> lP uP.
rewrite /= /contiguous_intervals1 /contiguous_intervals2.
apply/trivIsetP => i j _ _ ij.
have [->|/set0P ?]  := eqVneq (contiguous_intervals P i) set0.
  by rewrite inf0 sup0 set_itv_ge ?bnd_simp// set0I.
have [->|/set0P ?]  := eqVneq (contiguous_intervals P j) set0.
  by rewrite inf0 sup0 setIC set_itv_ge ?bnd_simp// set0I.
have /trivIsetP/(_ i j Logic.I Logic.I ij) := @disjoint_contiguous_intervals _ P.
apply: subsetI_eq0. (* TODO: generalize this lemma to trivIset *)
- have /is_intervalP H := @is_interval_contiguous_intervals _ P i.
  rewrite [X in _ `<=` X]H.
   apply: interval_ooS.
   rewrite has_bound_inf_sup//.
   by apply: has_lbound_contiguous_intervals.
   by apply: has_ubound_contiguous_intervals.
- have /is_intervalP H := @is_interval_contiguous_intervals _ P j.
  rewrite [X in _ `<=` X]H.
  apply: interval_ooS.
  rewrite has_bound_inf_sup//.
  by apply: has_lbound_contiguous_intervals.
  by apply: has_ubound_contiguous_intervals.
Qed.

End lemma4_preliminaries.

Section lemma4.
Context {R: realType}.
Variables a b : R.
Hypothesis ab : a <= b.
Local Notation mu := (@completed_lebesgue_measure R).
Local Open Scope ereal_scope.

Lemma lemma4 (f : R -> R) (P : set R) :
  is_interval (f @` `[a, b]) ->
  (* perfect_set P *) closed P ->
 (*  a = inf P -> b = sup P -> *)
  Rhull P = `[a, b] ->
  let a_ := contiguous_intervals1 P in
  let b_ := contiguous_intervals2 P in
  `|f b - f a|%:E <= mu (f @` `[a, b])
     <= (mu^*)%mu (f @` P) +
        \sum_(0 <= i <oo) oscillation f `[(a_ i), (b_ i)]%classic.
Proof.
move=> fab closedP.
move/[dup]/eq_Rhull_itvccP => [[haslbP Pinf infa] [hasubP Psup supa]] Pab.
have compactP : compact P.
  apply: Rbounded_closed_compact => //.
  by rewrite Rbounded_setE.
set a_ := contiguous_intervals1 P.
set b_ := contiguous_intervals2 P.
have H1 : f @` `[a, b] = (f @` P) `|` \bigcup_i f @` `](a_ i), (b_ i)[.
  rewrite -image_bigcup_disjoint; last first.
    exact: trivIset_contiguous_intervals.
  rewrite -image_setU.
  congr (f @` _).
  apply/seteqP; split; last first.
    rewrite -Pab.
    rewrite subUset; split; first exact: sub_Rhull.
    apply: bigcup_sub => i _.
    have -> : `]((a_ i)), ((b_ i))[%classic =
                   [set` Rhull (contiguous_intervals P i)].
      rewrite /Rhull.
      rewrite ifT; last exact/asboolP/has_lbound_contiguous_intervals.
      rewrite ifT; last exact/asboolP/has_ubound_contiguous_intervals.
      congr ([set` Interval (BSide _ _) (BSide _ _)]); apply: eq_fun => _.
      - apply/esym/asboolF.
        apply: open_haslb_memNinf.
        + exact: has_lbound_contiguous_intervals.
        + exact: open_contiguous_intervals.
      - apply/esym/asboolP.
        apply: open_hasub_memNsup.
        + exact: has_ubound_contiguous_intervals.
        + exact: open_contiguous_intervals.
    rewrite RhullK; last first.
      rewrite inE.
      exact: is_interval_contiguous_intervals.
    apply: (subset_trans (@contiguous_intervalsS _ P i)).
    exact: cplt_hull_subset_Rhull.
  rewrite /a_.
  rewrite -bigcup_contiguous_intervals_fine//.
  rewrite setDUK; last exact: sub_Rhull.
  by rewrite Pab.
apply/andP; split.
  (* wlog? *)
  have [fafb|] := pselect (f a < f b)%R.
    have -> : `|f b - f a|%:E = mu `[f a, f b].
      rewrite completed_lebesgue_measure_itv/= lte_fin fafb -EFinD.
      move: fafb.
      rewrite -subr_gt0.
      by move/ltW/normr_idP ->.
    apply: le_outer_measure => /= x/= xfab.
    apply: (fab (f a) (f b)).
    - by exists a => //=; rewrite bound_itvE.
    - by exists b => //=; rewrite bound_itvE.
    - by rewrite in_itv/= in xfab.
    move/negP; rewrite -leNgt.
    rewrite le_eqVlt => /predU1P[-> |].
      by rewrite subrr normr0 measure_ge0.
  rewrite -normrN opprB => fbfa.
  have -> : `|f a - f b|%:E = mu `[f b, f a].
    rewrite completed_lebesgue_measure_itv/= lte_fin fbfa -EFinD.
    move: fbfa.
    rewrite -subr_gt0.
    by move/ltW/normr_idP ->.
  apply: le_outer_measure => /= x/= xfba.
  apply: (fab (f b) (f a)).
  - by exists b => //=; rewrite bound_itvE.
  - by exists a => //=; rewrite bound_itvE.
  - by rewrite in_itv/= in xfba.
rewrite -measurable_mu_extE; last first.
  apply: sub_caratheodory.
  rewrite -(@RhullK _ (f @` `[a, b]))//.
  by rewrite inE.
rewrite H1.
apply: (@le_trans _ _ (mu^*%mu [set f x | x in P] +
         mu^*%mu (\bigcup_i [set f x | x in `](a_ i), (b_ i)[]))).
  exact: outer_measureU2.
apply: leeD2l.
apply: le_trans.
  exact: outer_measure_sigma_subadditive.
rewrite /=.
apply: lee_nneseries; first by move=> i _ _; exact: outer_measure_ge0.
move=> n _.
rewrite /oscillation.
case: ifPn => [/eqP ab0|ab0].
  have anbn : ((a_ n) > (b_ n))%R.
    rewrite ltNge; contra: ab0 => anbn.
    apply/set0P; exists ((a_ n)).
    by rewrite /= in_itv/= lexx anbn.
  rewrite set_itv_ge ?bnd_simp -?leNgt//; last exact/ltW.
  by rewrite image_set0 mu_ext0.
rewrite [leRHS](_ : _ =
       mu^*%mu [set` Rhull (f @` `[((a_ n)), ((b_ n))] )]).
  apply: le_outer_measure.
  apply: subset_trans (@sub_Rhull _ _).
  apply: image_subset.
  exact: subset_itv_oo_cc.
rewrite measurable_mu_extE/=; last first.
  apply: sub_caratheodory.
  exact: measurable_itv.
rewrite completed_lebesgue_measure_itv.
have fab0 : [set f x | x in `[((a_ n)), ((b_ n))]] !=set0.
  exists (f ((a_ n))) => //.
  exists ((a_ n)) => //=.
  rewrite boundl_in_itv//= bnd_simp.
  exact: contiguous_intervals1_le_contiguous_intervals2.
have [hasubf|hasNubf] :=
  pselect (has_ubound (f @` `[((a_ n)), ((b_ n))])); last first.
  rewrite -image_comp hasNub_ereal_sup//.
  rewrite addye; last first.
    apply/eqP.
    move/eqe_oppLRP => /=.
    move/ereal_inf_pinfty.
    apply/not_forallP; rewrite not_notE.
    have [y [x/= xab fax]] := fab0.
    by exists y%:E; rewrite ?not_implyP; split => //; exists y => //; exists x.
  rewrite ifT; last first.
    rewrite /=; move/asboolF : (hasNubf) => ->.
    by case: ifP => // _; exact: ltry.
  rewrite /=; move/asboolF : (hasNubf) => ->.
  by case: ifP.
have [haslbf|hasNlbf] :=
   pselect (has_lbound (f @` `[((a_ n)), ((b_ n))])); last first.
  rewrite -[X in _ - ereal_inf X = _]image_comp hasNlb_ereal_inf//; last first.
  rewrite ifT; last first.
    rewrite /=; move/asboolF: (hasNlbf) => ->.
    move/asboolP: (hasubf) => ->; exact: ltNyr.
  rewrite /=; move/asboolF: (hasNlbf) => -> /=.
  have supNy: ereal_sup ((EFin \o f) @` `[((a_ n)), ((b_ n))]) != -oo.
    apply/eqP; move/ereal_sup_ninfty; apply/not_forallP; rewrite not_notE.
    have [y [x/= xab fax]] := fab0.
    by exists y%:E; rewrite ?not_implyP; split => //; exists x=> //; congr EFin.
  by case: ifP; rewrite addey.
rewrite /Rhull; move/asboolP: (hasubf) ->; move/asboolP: (haslbf) -> => //.
case: ifP => /=; last first.
- move/negP/negP; rewrite -leNgt.
  rewrite le_eqVlt => /predU1P[|]; last first.
  + rewrite lte_fin ltNge => /negP Ninfsup.
    by have := has_bound_inf_sup fab0 haslbf hasubf.
  + rewrite -ereal_sup_EFin -?ereal_inf_EFin// image_comp => ->;
    rewrite subee//.
    by rewrite -image_comp ereal_inf_EFin.
- move=> _; rewrite EFinN -ereal_sup_EFin -?ereal_inf_EFin// 2?image_comp//.
Qed.

Local Close Scope ereal_scope.

Let ex_perfect_set (cmf : cumulative R R) (cZ : set R) :
  let f := cmf in
  cZ `<=` `[a, b] ->
  {within `[a, b], continuous f} ->
  {in `[a, b], {homo f : x y / (x <= y)}} ->
  bounded_variation a b f ->
  exists n, exists I : nat -> R * R,
  (forall i, trivIset setT (fun i => `[(I i).1, (I i).2]%classic) /\
    `](I i).1, (I i).2[ `<=` cZ) /\
     (\sum_(0 <= i < n) `|f (I i).2 - f (I i).1|)%:E
     = completed_lebesgue_stieltjes_measure f cZ.
Proof.
Abort.

End lemma4.
