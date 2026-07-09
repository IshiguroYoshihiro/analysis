From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality.
From mathcomp Require Import reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure realfun.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import borel_hierarchy absolute_continuity.
From mathcomp Require Import banach_zarecki_lemma2.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 3)                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma cvg_half {R : realType} : (2^-1 ^+ x) @[x --> \oo] --> (0 : R).
Proof.
rewrite (_:(fun n => (2^-1 ^+ n)) = (fun n => geometric 1 2^-1 n)).
   apply: funext => n.
   by rewrite /geometric/= mul1r.
apply: cvg_geometric.
rewrite ger0_norm// invf_lt1//.
exact: ltr1n.
Qed.

Lemma continuous_increasing_set_bij {R : realType} (f : R -> R) a b (ab : a < b) :
  {within `[a, b], continuous f} ->
  {in `[a, b] &, {homo f : x y / x < y}} ->
  set_bij `[a, b] `[f a, f b] f.
Proof.
move=> cf incf.
split.
- move=> x/=; rewrite 2!in_itv/= => /andP[ax xb]; apply/andP; split.
  + move: ax; rewrite le_eqVlt => /predU1P[-> //|ax].
    apply/ltW/incf; rewrite ?in_itv//=.
    * by rewrite lexx (ltW ab).
    * by rewrite xb andbT ltW.
  + move: xb; rewrite le_eqVlt => /predU1P[-> //|xb].
    apply/ltW/incf; rewrite ?in_itv//=.
    * by rewrite ax/= ltW.
    * by rewrite lexx (ltW ab).
- move=> x y; rewrite 2!inE/= 2!in_itv/= => /andP[ax xb]/andP[ay yb].
  move/eqP; rewrite eq_le => /andP[fxy fyx].
  apply/not_notP => /eqP.
  rewrite neq_lt => /orP[xy|yx].
  + move: fyx => /not_notP; apply.
    apply/negP; rewrite lt_geF//.
    apply: incf; rewrite ?in_itv//=.
    * by rewrite ax xb.
    * by rewrite ay yb.
  + move: fxy => /not_notP; apply.
    apply/negP; rewrite lt_geF//.
    apply: incf; rewrite ?in_itv//=.
    * by rewrite ay yb.
    * by rewrite ax xb.
- apply: segment_continuous_le_surjective => //.
  + exact: ltW.
  + by apply/ltW/incf; rewrite //?boundl_in_itv ?boundr_in_itv bnd_simp/= ltW.
Qed.

Lemma continuous_increasing_image_itv {R : realType} (f : R -> R) a b (ab : a < b) :
  {within `[a, b], continuous f} ->
  {in `[a, b] &, {homo f : x y / x < y}} ->
  f @` `[a, b] = `[f a, f b]%classic.
Proof.
move=> cf incf.
rewrite eqEsubset; split.
  apply: set_bij_sub.
  exact: continuous_increasing_set_bij.
rewrite -surjE.
apply: set_bij_surj.
exact: continuous_increasing_set_bij.
Qed.

Lemma GdeltaIr {T : topologicalType} (U S : set T) : open U ->
  Gdelta S -> Gdelta (U `&` S).
Proof.
move=> oU [V_ oV {S}->]; exists (fun n => if n == 0 then U else V_ n.-1).
- by case.
- by rewrite [RHS](bigcap_splitn 1)/= big_ord1.
Qed.

Lemma GdeltaIl {T : topologicalType} (U S : set T) : open U ->
  Gdelta S -> Gdelta (S `&` U).
Proof. by move=> oU GS; rewrite setIC; exact: GdeltaIr. Qed.

Lemma isolatedP {T : topologicalType} (A : set T) (x : T) :
 isolated A x ->
  x \in A /\ exists2 V, open_nbhs x V & V `&` A = [set x].
Proof.
move=> [zA [V xV VAx]].
split => //.
move: xV; rewrite nbhsE/= => -[B xB BV].
exists B => //.
apply/seteqP; split => [z [Bz Az]|].
  by rewrite -VAx; split => //; exact: BV.
move=> z/= ?; subst z.
move/seteqP : VAx => [_ /(_ x erefl)[Vx Ax]].
split => //.
by case: xB.
Qed.

From mathcomp Require Import rat.

Section perfect_set_rm.
Context {R : realType}.
Let mu := @lebesgue_measure R.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

Definition oobasis : set (set R) := [set `]ratr x.1, ratr x.2[ | x in setT].

Lemma set0_oobasis : set0 \in oobasis.
Proof.
rewrite inE /oobasis/=.
exists (1, 0)%R => //=.
rewrite -subset0 => x/=; rewrite in_itv/= => /andP[/lt_trans] => /[apply].
by rewrite ltr_rat ltr10.
Qed.

Lemma oobasis_countable : countable oobasis.
Proof.
by rewrite /countable -(card_le_eqr card_rat2); exact: card_image_le.
Qed.

Lemma oobasis_basis : basis oobasis.
Proof.
split; first by move=> A [[a b]] _/= <-; exact: itv_open.
move=> r V; rewrite nbhsE/= => -[U [oU /mem_set Ur] UV].
have [a [b [_ [rB BU]]]] := open_subball_rat oU Ur.
exists (@ball _ R (ratr a) (ratr b)) => /=; last exact: subset_trans UV.
split; last exact/set_mem.
by exists (a - b, a + b)%R => //=; rewrite ball_itv raddfB/= raddfD.
Qed.

Lemma Rsecond_countable : @second_countable R.
Proof. by exists oobasis; [exact: oobasis_countable|exact: oobasis_basis]. Qed.

Definition rat_itv (U : set R) := [set pq : (rat * rat)%type |
  (pq.1 < pq.2)%R /\ `]ratr pq.1, ratr pq.2[ `<=` U].

Lemma open_rat_itv (U : set R) : open U ->
  U = \bigcup_(pq in rat_itv U) `]ratr pq.1, ratr pq.2[.
Proof.
move=> openU.
apply/seteqP; split => [x /mem_set Ux|z [i [i12 + iz]]]; last exact.
suff [[p q] Bpq /=xpq] : exists2 pq : (rat * rat)%type,
    pq \in rat_itv U & x \in `]ratr pq.1, ratr pq.2[.
  by exists (p, q) => //=; [exact: set_mem|by rewrite inE in xpq].
have [a [b [r0 [xB BU]]]] := open_subball_rat openU Ux.
exists (a - b, a + b)%R.
  rewrite inE /rat_itv /=; split => //.
    by rewrite ltrBlDr -addrA ltrDl addr_gt0.
  by rewrite raddfB/= raddfD/= -ball_itv.
rewrite inE/= raddfB/= raddfD/=.
by move: xB; rewrite ball_itv inE.
Qed.

Lemma perfect_set_rm (X : set R) :
  compact X -> mu X < +oo ->
  exists B, [/\ B `<=` X, compact B, isolated B = set0 &
    mu B = mu X].
Proof.
move=> compactX boundedX.
pose G : set R := \bigcup_(U in [set U | open U /\ mu (X `&` U) = 0]) U.
have openG : open G.
  rewrite /G.
  by apply: bigcup_open => ? [].
pose K := X `\` G.
have mG : measurable G by exact: open_measurable.
have mX : measurable X by exact: compact_measurable.
have compactK : compact K.
  rewrite /K.
  rewrite setDE.
  apply: compact_closedI => //.
  by apply: open_closedC.
have G0 : mu (X `&` G) = 0.
  have [F [Fbasis F0] GF] : exists2 F : (set R)^nat,
      (forall i, F i \in oobasis) /\ (forall i, mu (X `&` F i) = 0) &
      G = \bigcup_i F i.
    have GE : G = \bigcup_(U in [set U | oobasis U /\ mu (X `&` U) = 0%R]) U.
      apply/seteqP; split => [r [/= A [oA XA0]]|r].
        rewrite (open_rat_itv oA) => -[pq Apq rpq].
        exists (`]ratr pq.1, ratr pq.2[) => //=.
        split; first by exists pq.
        rewrite /rat_itv /= in Apq.
        apply/eqP; rewrite eq_le measure_ge0 andbT.
        rewrite -XA0 le_measure//= ?inE//=.
          exact: measurableI.
          by apply: measurableI => //; exact: open_measurable.
        by apply: setIS; case: Apq.
      move=> [_/= [[pq _ <-]]] Xpq pqr.
      by exists `]ratr pq.1, ratr pq.2[.
    have /countable_bijP[B] := oobasis_countable.
    (* TODO: write this down in the FAQ *)
    rewrite card_eq_sym => /card_set_bijP[f/=] bijf.
    Check f : nat -> set R.
    pose f1 : set R -> nat := pinv B f.
    exists (fun n => if (n \in B) && (mu (X `&` f n) == 0) then
      f n else set0).
      split.
        move=> n.
        case: ifPn.
          move=> /andP[/set_mem Bn _].
          apply/mem_set.
          case: bijf => + _ _.
          by apply.
        by rewrite set0_oobasis.
      move=> i.
      case: ifPn=> [|_].
        by move=> /andP[_ /eqP].
      by rewrite setI0 [LHS]measure0.
    rewrite GE.
    rewrite bigcup_mkcondr.
    rewrite (reindex_bigcup f B)//.
      by case: bijf.
      by case: bijf.
    rewrite bigcup_mkcond.
    apply: eq_bigcup => //= i _.
    case: ifPn => //= Bi.
    rewrite /mem/= /in_mem/= /in_set/=.
    by case: asboolP => [->|/eqP/negPf ->//]; rewrite eqxx.
  rewrite GF.
  rewrite setI_bigcupr.
  apply/eqP; rewrite eq_le.
  rewrite measure_ge0 andbT.
  apply: (@le_trans _ _ (\sum_(0 <= i <oo) mu (X `&` F i))).
    exact: outer_measure_sigma_subadditive.
  by rewrite eseries0//.
have muKX : mu K = mu X.
  rewrite /K.
  rewrite [LHS]measureD//= -/mu.
    by rewrite G0 sube0.
have isoK : isolated K = set0.
  rewrite -subset0 => /= x.
  move/isolatedP => [xK /= [U xU UKx]].
  have xG : x \notin G by move: xK; rewrite in_setD => /andP[].
  have mXU0 : mu (X `&` U) > 0.
    rewrite lt_neqAle measure_ge0 andbT eq_sym.
    apply/eqP => XU0.
    have UG : U `<=` G.
      rewrite /G.
      apply: bigcup_sup => /=; split => //.
      by case: xU.
    move/negP : xG; apply.
    apply/mem_set/UG.
    by case: xU.
  have : 0 < mu (K `&` U).
    rewrite /K.
    rewrite setDE.
    rewrite setIAC.
    rewrite -setDE.
    have mU : measurable U by apply: open_measurable; case: xU.
    rewrite [ltRHS](@measureD _ _ _ mu (X `&` U) G)//.
      exact: measurableI.
      rewrite (le_lt_trans _ boundedX)// le_measure// ?inE//.
      exact: measurableI.
    have XUG0 : mu (X `&` U `&` G) = 0.
      apply/eqP.
      rewrite eq_le measure_ge0 andbT.
      rewrite -G0.
      rewrite le_measure// ?inE.
      by apply: measurableI => //; apply: measurableI.
      by apply: measurableI => //.
      rewrite setIAC.
      exact: subIsetl.
    by rewrite [X in _ - X]XUG0 sube0.
  by rewrite setIC UKx /mu lebesgue_measure_set1 ltxx.
exists K.
split.
- exact: subDsetl.
- assumption.
- assumption.
- by rewrite muKX.
Qed.

End perfect_set_rm.

Section lemma3.
Context {R : realType}.
Variables a b : R.
Hypothesis ab : a < b.

Local Notation mu := (@completed_lebesgue_measure R).

(* lemma3 (easy direction) *)
Lemma Lusin_image_measure0 (f : R -> R) :
  {within `[a, b], continuous f} ->
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  lusinN `[a, b] f ->
  forall Z : set R, [/\ Z `<=` `[a, b]%classic,
      compact Z &
      mu Z = 0] ->
      mu (f @` Z) = 0.
Proof.
move=> cf ndf lusinNf Z [Zab cZ muZ0].
have /= mZ : (wlength idfun)^*%mu.-cara.-measurable Z.
  by apply: sub_caratheodory; exact: compact_measurable.
exact: (lusinNf Z Zab mZ muZ0).
Qed.

Lemma lebesgue_measure_Gdelta_approx (Z : set R) :
  ((wlength idfun)^*%mu Z < +oo)%E ->
  exists U : (set R)^nat, [/\ (forall k, Z `<=` U k), (forall k, open (U k)),
    {homo U : n m / (n <= m)%N >-> (m <= n)%O} &
    (wlength idfun)^*%mu Z = (wlength idfun)^*%mu (\bigcap_k U k)].
Proof.
move=> Zoo.
pose delta k := 2^-1 ^+ k :> R.
have delta_gt0 k : 0 < delta k by rewrite exprn_gt0.
pose Us : set (set R) := [set U | open U /\ Z `<=` U].
have mUfin : ereal_inf [set mu U | U in Us] \is a fin_num.
  by rewrite -lebesgue_regularity_outer_inf ge0_fin_numE.
have := fun k => (@exists2P _ _ _).1
  (@lb_ereal_inf_adherent _ [set mu U | U in Us] _ (delta_gt0 k) mUfin).
move/(@choice _ _ (fun k x => [set mu U | U in Us] x /\
     (x < ereal_inf [set mu U | U in Us] + (delta k)%:E)%E)).
move=> [e_] /all_and2[/= + einf].
under [X in X -> _]eq_forall do rewrite exists2E.
move=> /choice[U_].
move=> /all_and2[/all_and2[oU ZU] mUe].
pose V_ := fun n => \bigcap_(i < n.+1) U_ i.
have niV : {homo V_ : n m / (n <= m)%N >-> (m <= n)%O}.
  apply/nonincreasing_seqP => n.
  rewrite /V_ !bigcap_mkord.
  rewrite big_ord_recr/= subsetEset.
  exact: subIsetl.
exists V_; split.
- by move=> n; exact: sub_bigcap.
- by move=> n; exact: bigcap_open.
- exact: niV.
- rewrite [X in _ = _ X](_ : _ = \bigcap_i U_ i).
    rewrite eqEsubset; split.
      move=> x Hx n _.
      by apply: (Hx n.+1) => /=.
    move=> x + n _ k /= kn.
    exact.
  have V0oo : (mu (V_ 0%N) < +oo)%E.
    rewrite /V_ bigcap1 (mUe 0%N) (lt_trans (einf 0%N))//.
    apply: lte_add_pinfty; last by exact: ltry.
    by rewrite -lebesgue_regularity_outer_inf.
  have mV i : measurable (V_ i).
    apply: bigcap_measurable.
      by exists 0%N.
    move=> k /= _.
    exact: open_measurable.
  have mIV : measurable (\bigcap_i V_ i) by exact: bigcap_measurable.
  have pVE n : \bigcap_(i < n) V_ i = \bigcap_(i < n) U_ i.
    case: n.
      by rewrite eqEsubset; split.
    move=> n.
    rewrite eqEsubset; split.
      move=> x Vx k/= kn.
      by apply: (Vx k) => /=.
    move=> x HU k /= kn m /= mk.
    apply: (HU m) => /=.
    exact: leq_trans _ kn.
  have VE : \bigcap_i V_ i = \bigcap_i U_ i.
    rewrite eqEsubset; split.
      move=> x HV n _.
      apply: (HV n) => //.
      by rewrite IIS; right.
    move=> x HU n _ k /= kn.
    exact: (HU k).
  rewrite -VE.
  apply: esym.
  have /cvg_lim VIV :=
    @nonincreasing_cvg_mu _ _ _ lebesgue_measure V_ V0oo mV mIV niV.
  rewrite -[LHS]VIV//.
  apply: cvg_lim => //.
  apply: (@squeeze_cvge _ _ _ _ (cst (mu Z)) _ (fun n => mu Z + (delta n)%:E)%E).
  - apply: nearW => n/=; apply/andP; split.
      apply: le_outer_measure.
      move=> x Zx k/= _.
      exact: ZU.
    apply: (@le_trans _ _ (mu (U_ n))).
      rewrite le_outer_measure//.
      by apply: bigcap_inf => /=.
    rewrite mUe completed_lebesgue_measureE lebesgue_regularity_outer_inf ltW//.
    exact: einf.
  - exact: cvg_cst.
  - rewrite -(adde0 ((wlength _)^*%mu Z)).
    apply: cvgeD.
    + exact: fin_num_adde_defl.
    + exact: cvg_cst.
    + by apply: cvg_EFin; [exact: nearW|exact: cvg_half].
Qed.

Let measurable_image_setI_set1 (f : R -> R) (A : set R) (x : R) :
  measurable (f @` (A `&` [set x])).
Proof.
rewrite setI1; case: ifP; rewrite ?image_set0// image_set1 => _.
exact: measurable_set1.
Qed.

Let measurable_setD1 (A : set R) (x : R) :
  measurable A -> measurable (A `\ x).
Proof.
move=> mA.
rewrite setDE.
apply: measurableI => //.
apply: measurableC.
exact: measurable_set1.
Qed.

Let image_setD1 (f : R -> R) (A : set R) (x : R) :
(forall a, (A `\ x) a -> f a != f x) ->
  f @` (A `\ x) = (f @` A) `\ f x.
Proof.
move=> H.
rewrite eqEsubset; split.
  move=> _ [z [Az /= zx] <-]; split; first by exists z.
  apply/eqP; exact: H.
move=> _ [[z Az <-] /= fzx].
exists z => //; split => //.
move=> zx; apply: fzx.
by f_equal.
Qed.

Let not_image_setD1 (f : R -> R) (A : set R) (x : R) :
 ~ (forall a, (A `\ x) a -> f a != f x) ->
  f @` (A `\ x) = (f @` A).
Proof.
move=> H.
rewrite eqEsubset; split.
  apply: image_subset.
  exact: subDsetl.
have [Ax|nAx] := pselect (A x); last by rewrite not_setD1.
rewrite -{1}(setD1K Ax).
move=> y [z + <-].
case.
  move->.
  move: H.
  move/existsNP => [t].
  move/not_implyP => [[At /= tx]].
  move/negP/negPn/eqP => ftx.
  by exists t.
move=> [Az /= zx].
by exists z.
Qed.

Let measurable_image_setD1 (f : R -> R) (A : set R) (x : R) :
  measurable (f @` A) ->
  measurable (f @` (A `\ x)).
Proof.
move=> mfA.
have [Ax|nAx] := pselect (forall a, (A `\ x) a -> f a != f x).
  by rewrite image_setD1//; apply: measurableD.
by rewrite not_image_setD1.
Qed.

Let measure0_image_setI_set1 (f : R -> R) (A : set R) (x : R) :
  mu (f @` (A `&` [set x])) = 0.
Proof.
rewrite setI1; case: ifP; rewrite ?image_set0// image_set1 => _.
exact: lebesgue_measure_set1.
Qed.

Let measure0_setI_set1 (A : set R) (x : R) :
  mu (A `&` [set x]) = 0.
Proof.
rewrite setI1; case: ifP => //.
by rewrite completed_lebesgue_measureE lebesgue_measure_set1.
Qed.

(* generalize? *)
Let measure_image_setD_set1 (f : R -> R) (A : set R) (x : R) :
  mu (f @` (A `\ x)) = mu (f @` A).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: le_outer_measure.
  rewrite setDE.
  apply: (subset_trans sub_image_setI).
  exact: subIsetl.
rewrite -{1}(setUIDK A [set x]).
rewrite image_setU.
apply: (le_trans (outer_measureU2 _ _ _)) => /=.
have := measure0_image_setI_set1 f A x.
rewrite completed_lebesgue_measureE.
rewrite /lebesgue_measure/lebesgue_stieltjes_measure/measure_extension.
by move->; rewrite add0r.
Qed.

(* testing strict increasing version *)
Lemma image_measure0_Lusin_increasing (F : R -> R) :
  {within `[a, b], continuous F} ->
  {in `[a, b] &, {homo F : x y / x < y}} ->
  (forall Z : set R, Z `<=` `[a, b]%classic ->
      compact Z ->
      mu Z = 0 ->
      mu (F @` Z) = 0) ->
  lusinN `[a, b] F.
Proof.
move=> cF incF lusinN'.
apply: contrapT.
move=> /existsNP[Z]/not_implyP[Zab/=] /not_implyP[mZ] /not_implyP[muZ0].
move=> /eqP; rewrite neq_lt ltNge measure_ge0/= => muFZ0.
have Zoo : (mu Z < +oo)%E.
  apply: (@le_lt_trans _ _ (mu `[a, b])); first exact: le_outer_measure.
  rewrite completed_lebesgue_measureE.
  by rewrite lebesgue_measure_itv/= lte_fin ab -EFinD ltry.
have [U_ [ZU oU _ mZIU]] := lebesgue_measure_Gdelta_approx Zoo.
set Z1 := `]a, b[ `&` \bigcap_n U_ n.
have muZ10 : mu Z1 = 0.
  apply/eqP; rewrite -measure_le0/= -muZ0.
  rewrite completed_lebesgue_measureE.
  rewrite /lebesgue_measure/lebesgue_stieltjes_measure/measure_extension mZIU.
  apply: le_outer_measure.
  exact: subIsetr.
have Z1ab : Z1 `<=` `]a, b[ by exact: subIsetl.
have Z1oo : (mu (F @` Z1) < +oo)%E.
  apply: (@le_lt_trans _ _ (mu (F @` `[a, b]))).
    apply: le_outer_measure.
    apply: image_subset.
    apply: (subset_trans Z1ab).
    exact: subset_itv_oo_cc.
  rewrite continuous_increasing_image_itv//.
  rewrite completed_lebesgue_measure_itv lte_fin incF// -?EFinB ?ltry//.
    by rewrite boundl_in_itv/= bnd_simp ltW.
  by rewrite boundr_in_itv bnd_simp ltW.
have gZ1 : Gdelta Z1.
  apply: GdeltaIr => //.
  by exists U_.
(* using lemma2 *)
have mFZ1 : measurable (F @` Z1).
apply: measurable_image_Gdelta_set_nondecreasing_fun Z1ab gZ1 => //.
  by move=> ? ? ? ?; rewrite le_eqVlt => /predU1P[->//|xy]; exact/ltW/incF.
have ZZ1 : Z `\ a `\ b `<=` Z1.
  rewrite subsetI; split.
  - rewrite -(setIidr Zab).
    rewrite -(setU1itv false) ?bnd_simp ?ltW//.
    rewrite setIUl setDUl.
    rewrite setIC -setIDA setDv setI0 set0U.
    rewrite -(setUitv1 true) ?bnd_simp ?ltW//.
    rewrite setIUl 2!setDUl -2!setIDA.
    rewrite -setIDA (setIC [set b]) -setIDA setDv setI0 setU0.
    exact: subIsetl.
  - apply: sub_bigcap => n _.
    apply: subset_trans (ZU n).
    rewrite setDDl.
    exact: subDsetl.
have FZ1oo : (mu (F @` Z1) < +oo)%E.
  apply: (@le_lt_trans _ _ (mu (F @` `]a, b[))).
    apply: le_outer_measure.
    exact: image_subset.
  apply: (@le_lt_trans _ _ (mu `[F a, F b])).
    apply: le_outer_measure.
    rewrite -continuous_increasing_image_itv => //.
    apply: image_subset.
    exact: subset_itv_oo_cc.
  rewrite completed_lebesgue_measure_itv.
  by case: ifP=> //; rewrite -EFinB ltry.
have FZ10 : (0 < mu (F @` Z1))%E.
  apply: (@lt_le_trans _ _ (mu (F @` (Z `\ a `\ b)))).
    by rewrite 2!measure_image_setD_set1.
  apply: le_outer_measure.
  exact: image_subset.
set e := fine (mu (F @` Z1)) / 2.
have e0 : 0 < e by rewrite divr_gt0 ?fine_gt0 ?FZ1oo ?FZ10.
have [K [cK KFZ1 Z1Ke]] := lebesgue_regularity_inner mFZ1 FZ1oo e0.
set K1 := `[a, b] `&` F @^-1` K.
have K1K : F @` K1 = K.
  rewrite eqEsubset; split.
    apply: (subset_trans sub_image_setI).
    apply: subIset; right.
    exact: image_preimage_subset.
  move=> r Kr/=.
  pose L := `[a, b] `&` preimage F [set r].
  have L0 : L !=set0.
    have [] := @IVT _ _ _ _ r (ltW ab) cF.
      have Fab : F a < F b.
        apply: incF => //.
        - by rewrite boundl_in_itv bnd_simp ltW.
        - by rewrite boundr_in_itv bnd_simp ltW.
      rewrite minElt Fab.
      rewrite maxElt Fab.
      move: Kr => /KFZ1[t [/= tab _] <-].
      rewrite 2?ltW ?incF//.
      - by rewrite bound_itvE// ltW.
      - exact: subset_itv_oo_cc.
      - by move: tab; rewrite in_itv/= => /andP[].
      - exact: subset_itv_oo_cc.
      - by rewrite bound_itvE// ltW.
      - by move: tab; rewrite in_itv/= => /andP[].
    by move=> x xab; rewrite /L; move <-; exists x.
  move: (L0) => [r'] /[dup] Lr'.
  rewrite /L/= => [[r'ab Fr'r]].
  exists r' => //.
  rewrite /K1/=; split => //.
  by rewrite Fr'r.
have : (0 < mu (F @` K1))%E.
  rewrite K1K.
  have := Z1Ke.
  rewrite measureD//; first exact: compact_measurable.
  rewrite setIidr//.
  rewrite lteBlDl.
    rewrite ge0_fin_numE//.
    apply: le_lt_trans FZ1oo.
    exact: le_outer_measure.
  rewrite -lteBlDr//.
  rewrite completed_lebesgue_measureE.
  apply: le_lt_trans.
  rewrite sube_ge0// /e EFinM fineK; first by rewrite ge0_fin_numE.
  rewrite muleC gee_pMl//.
  rewrite lee_fin invf_le1//.
  by rewrite -[leLHS](mulr1n 1) ler_nat.
apply/negP.
rewrite -leNgt.
rewrite measure_le0/=.
apply/eqP.
apply: lusinN'.
- exact: subIsetl.
- rewrite /K1 setIC.
  rewrite -(setIid `[a, b]%classic) setICA.
  apply: compact_closedI => //; first exact: segment_compact.
  rewrite closed_setIS; first exact: interval_closed.
  apply: (continuous_closedP _).1 => //.
  exact: compact_closed.
- apply/eqP; rewrite -measure_le0/= -muZ10.
  have bijF := continuous_increasing_set_bij ab cF incF.
  have [F' FF'] := pPbij bijF.
  rewrite /K1 FF' -inv_sub_image.
    apply: (subset_trans KFZ1).
    rewrite -continuous_increasing_image_itv//.
    apply: image_subset.
    apply: (subset_trans Z1ab).
    exact: subset_itv_oo_cc.
  apply: le_outer_measure.
  rewrite image_sub.
  apply: subset_trans (@inv_image_sub _ _ _ _ _ Z1 _) => /=; last first.
    apply: (subset_trans Z1ab).
    exact: subset_itv_oo_cc.
  rewrite invV.
  by move=> ? ?/=; rewrite -FF'; exact: KFZ1.
Abort.

  (* Lemma open_subset_itvoocc S : open S -> S `<=` `[a, b] -> S `<=` `]a, b[. *)
  (*   move=> oS Sab. *)
  (*   apply: (@subset_trans _ [set` Rhull S]). *)
  (*     exact: sub_Rhull. *)
  (*     (* lemma? *) *)
  (*   have itv_closure_subset : {in (@is_interval R) : set (set R) &, {mono closure : i j / i `<=` j}}. *)
  (*     move=> i j itvi itvj. *)
  (*     rewrite propeqE; split. *)
  (*       admit. *)
  (*     exact: closure_subset. *)
  (*   rewrite -itv_closure_subset; last 2 first. *)
  (*       admit. *)
  (*     admit. *)
  (*   rewrite closure_itvoo //. *)
  (*   (* lemma? *) *)
  (*   have closurer_subset X (x y : R) : X `<=` `[x, y] -> closure X `<=` `[x, y]. *)
  (*     admit. *)
  (*   apply: closurer_subset. *)
  (*   (* lemma? *) *)
  (*   have sub_Rhullr (i : interval R) : S `<=` [set` i] -> [set` Rhull S] `<=` [set` i]. *)
  (*     admit. *)
  (*   by apply: sub_Rhullr. *)


(* NB: available as PR https://github.com/math-comp/analysis/pull/1809 *)
Lemma compact_unif_continuousP f :
  {within `[a, b], continuous f} <-> @unif_continuous (subspace `[a, b]) R f.
Proof.
Admitted.

Section main_lemma.

Lemma limit_point_open (U : set R) (p : R) :
  limit_point U p <-> forall V, open_nbhs p V ->
                         exists y : R, [/\ y != p, U y & V y].
Proof.
split.
  move=> Up /= V pV.
  apply: Up.
  by apply: open_nbhs_nbhs.
move=> /= H V.
rewrite nbhsE/= => -[A pA AV].
have [y [yp Uy Ay]] := H _ pA.
exists y; split => //.
by apply: AV.
Qed.

(* NB: this is too long! *)
Lemma nondecreasing_cont_isolated (F : R -> R) (K : set R) :
  compact K ->
  {within `[a, b], continuous F} ->
  {in `[a, b] &, {homo F : x y / x <= y}} ->
  isolated K = set0 ->
  let A := `[a, b] `&` F @^-1` K : set R in
  [set F x | x in A] = K ->
  isolated A = set0.
Proof.
move=> cK cF ndF isoK0 A AK.
apply/nonemptyPn => -[/= x].
move/isolatedP => [/=].
rewrite inE => -[/= xab].
set y := F x.
move=> KFx.
have : limit_point K y.
  have : (closure K) y by exact: subset_closure.
  by rewrite closure_isolated_limit_point isoK0 set0U.
move/limit_pointP => [y_ [y_K y_neq y_cvg]].
move=> -[V + VAx].
move/open_nbhs_nbhs.
rewrite /nbhs/= /nbhs_ball_ => -[d /= d0 xdV].
have [xa|[xb|{}xab]] : x = a \/ x = b \/ x \in `]a, b[.
  have : x \in `[a, b]%classic.
    by rewrite inE.
  rewrite -(setU1itv false) ?bnd_simp//; first exact/ltW.
  rewrite -(setUitv1 true) ?bnd_simp//.
  by rewrite setUA setUAC inE/= orA.
- subst x.
  pose d' := Num.min (d / 2) (b - a).
  have d'0 : 0 < d'.
    by rewrite /d' lt_min divr_gt0// subr_gt0.
  have : F a <= F (a + d').
    rewrite ndF//.
      rewrite in_itv/=; apply/andP; split.
        by rewrite lerDl ltW.
      by rewrite -lerBrDl ge_min lexx orbT.
    by rewrite lerDl ltW.
  rewrite le_eqVlt => /predU1P[FaFad'|FaFad'].
    have : (V `&` A) (a + d').
      split.
        apply: xdV.
        rewrite /ball_/=.
        rewrite opprD addrA subrr add0r normrN gtr0_norm//.
        by rewrite gt_min gtr_pMr// invf_lt1// ltr1n.
      rewrite /A/=; split.
        rewrite in_itv/= lerDl ltW//=.
        by rewrite -lerBrDl ge_min lexx orbT.
      rewrite -FaFad' -AK/=.
      by exists a => //.
    rewrite VAx/=.
    apply/eqP.
    by rewrite eq_sym lt_eqF// ltrDl.
  have [n /andP[Fayn ynFad']] : exists n, F a < y_ n < F (a + d').
    pose k := ((F (a + d') - F a) / 2).
    have k0 : 0 < k.
      by rewrite divr_gt0// subr_gt0.
    move/cvgrPdist_lt : y_cvg => /(_ _ k0)[n _]/(_ n (@leqnn n)).
    rewrite ltr_distlC => /andP[ykyn ynyk].
    exists n.
    apply/andP; split.
      rewrite lt_neqAle; apply/andP; split.
        by rewrite eq_sym y_neq.
      have := y_K (y_ n).
      move=> /(_ (imageT _ _)).
      rewrite -AK/= => -[x' Ax' <-].
      rewrite ndF//.
        move: Ax'.
        by rewrite /A/= => -[].
      move: Ax'.
      by rewrite /A/= => -[] /itvP ->.
    rewrite (lt_le_trans ynyk)//.
    rewrite -lerBrDl.
    rewrite /k -/y.
    rewrite ger_pMr.
      by rewrite subr_gt0.
    by rewrite invf_le1// ler1n//.
  have H3 : {within `[a, a + d'], continuous F}.
    apply: continuous_subspaceW cF.
    apply: subset_itv; rewrite bnd_simp//=.
    by rewrite -lerBrDl ge_min lexx orbT.
  have : Num.min (F a) (F (a + d')) <= y_ n <=
         Num.max (F a) (F (a + d')).
    by rewrite ge_min (ltW Fayn)/= le_max (ltW ynFad') orbT.
  have aad' : a <= a + d'.
    by rewrite lerDl ltW.
  move/IVT => /(_ aad' H3)[x' x'aad' Fx'yn].
  have : x' \in V `&` A.
    rewrite inE.
    split.
      apply: xdV.
      apply/set_mem.
      rewrite -[X in _ \in X]/(ball _ _).
      rewrite ball_itv inE/=.
      apply: subset_itv x'aad'; rewrite bnd_simp//=.
        by rewrite ltrBlDl ltrDr.
      by rewrite ltrD2l gt_min gtr_pMr// invf_lt1//= ltr1n.
    rewrite /A; split => //=.
      apply: subset_itvl x'aad'; rewrite bnd_simp -lerBrDl.
      by rewrite ge_min lexx orbT.
    rewrite Fx'yn.
    apply/y_K.
    by apply/imageT.
  rewrite VAx inE/= => x'x.
  subst x'.
  move/eqP : Fx'yn.
  apply/negP.
  rewrite eq_sym.
  exact: y_neq.
- subst x.
  pose d' := Num.min (d / 2) (b - a).
  have d'0 : 0 < d'.
    by rewrite /d' lt_min divr_gt0// subr_gt0.
  have : F (b - d') <= F b.
    rewrite ndF//.
      rewrite in_itv/=; apply/andP; split.
        by rewrite lerBrDl -lerBrDr ge_min lexx orbT.
      by rewrite lerBlDl lerDr// ltW.
     by rewrite lerBlDl lerDr// ltW.
  rewrite le_eqVlt => /predU1P[FbFbd'|FbFbd'].
    have : (V `&` A) (b - d').
      split.
        apply: xdV.
        rewrite /ball_/=.
        rewrite opprD addrA opprK subrr add0r gtr0_norm//.
        by rewrite gt_min gtr_pMr// invf_lt1// ltr1n.
      rewrite /A/=; split.
        rewrite in_itv/= lerBlDl lerDr (ltW d'0) andbT.
        by rewrite lerBrDr -lerBrDl ge_min lexx orbT.
      rewrite FbFbd' -AK/=.
      by exists b => //.
    rewrite VAx/=.
    apply/eqP.
    by rewrite eq_sym gt_eqF// ltrBlDl ltrDr.
  have [n /andP[Fbyn ynFbd']] : exists n, F (b - d') < y_ n < F b.
    pose k := ((F b - F (b - d')) / 2).
    have k0 : 0 < k by rewrite divr_gt0// subr_gt0.
    move/cvgrPdist_lt : y_cvg => /(_ _ k0)[n _]/(_ n (@leqnn n)).
    rewrite ltr_distlC => /andP[ykyn ynyk].
    exists n.
    apply/andP; split.
      rewrite (le_lt_trans _ ykyn)//.
      rewrite lerBrDr -lerBrDl /y.
      rewrite /k.
      rewrite ger_pMr.
        by rewrite subr_gt0.
      by rewrite invf_le1// ler1n//.
    rewrite lt_neqAle; apply/andP; split.
      by rewrite y_neq.
    have := y_K (y_ n).
    move=> /(_ (imageT _ _)).
    rewrite -AK/= => -[x' Ax' <-].
    rewrite ndF//.
      move: Ax'.
      by rewrite /A/= => -[].
    move: Ax'.
    by rewrite /A/= => -[] /itvP ->.
  have H3 : {within `[b - d', b], continuous F}.
    apply: continuous_subspaceW cF.
    apply: subset_itv; rewrite bnd_simp//=.
    by rewrite lerBrDl -lerBrDr ge_min lexx orbT.
  have : Num.min (F (b - d')) (F b) <= y_ n <=
         Num.max (F (b - d')) (F b).
    by rewrite ge_min (ltW Fbyn)/= le_max (ltW ynFbd') orbT.
  have bd'b : b - d' <= b.
    rewrite lerBlDl.
    by rewrite lerDr ltW.
  move/IVT => /(_ bd'b H3)[x' x'bd'b Fx'yn].
  have : x' \in V `&` A.
    rewrite inE.
    split.
      apply: xdV.
      apply/set_mem.
      rewrite -[X in _ \in X]/(ball _ _).
      rewrite ball_itv inE/=.
      apply: subset_itv x'bd'b; rewrite bnd_simp//=.
        by rewrite ltrD2l ltrN2 // gt_min gtr_pMr// invf_lt1//= ltr1n.
      by rewrite ltrDl.
    rewrite /A; split => //=.
      apply: subset_itvr x'bd'b; rewrite bnd_simp.
      rewrite lerBrDl -lerBrDr.
      by rewrite ge_min lexx orbT.
    rewrite Fx'yn.
    apply/y_K.
    by apply/imageT.
  rewrite VAx inE/= => x'x.
  subst x'.
  move/eqP : Fx'yn.
  apply/negP.
  rewrite eq_sym.
  exact: y_neq.
pose d' := Num.min (d/2) (Num.min (x - a) (b - x)).
have d'0 : 0 < d'.
  by rewrite lt_min divr_gt0//= lt_min !subr_gt0 !(itvP xab).
have axd' : a <= x - d'.
  by rewrite lerBrDl -lerBrDr !ge_min lexx/= orbT.
have xd'b : x + d' <= b.
  by rewrite -lerBrDl !ge_min lexx/= !orbT.
have xd'xd' : x - d' <= x + d'.
  by rewrite lerBlDr -addrA lerDl addr_ge0// ltW.
have xd'ab : ball x d' `<=` `[a, b].
  move=> z.
  rewrite ball_itv/=.
  by apply: subset_itv; rewrite bnd_simp.
have : F (x - d') <= F (x + d').
  apply: ndF => //.
  rewrite in_itv/=; apply/andP; split => //.
    by rewrite (le_trans _ xd'b)//.
  rewrite in_itv/=; apply/andP; split => //.
  by rewrite (le_trans axd').
have d'd : d' < d.
  by rewrite !gt_min gtr_pMr// invf_lt1// ltr1n.
have xBd'b : x - d' <= b.
  rewrite lerBlDl -lerBlDr !le_min.
  rewrite lerD2l lerN2 (ltW ab)/=.
  apply/andP; split.
    rewrite lerBlDl -lerBlDr (le_trans _ xd'b)//.
    rewrite lerD2l (@le_trans _ _ 0)//.
      by rewrite lerNl oppr0 divr_ge0// ltW.
    by rewrite ltW.
  rewrite lerBlDl addrA -lerBlDr opprK.
  by rewrite lerD// (itvP xab).
have axDd' : a <= x + d'.
  rewrite -lerBlDl !le_min.
  rewrite lerD2r (ltW ab) andbT.
  apply/andP; split.
    rewrite lerBlDl (le_trans axd')// lerD2l (@le_trans _ _ 0)//.
      by rewrite lerNl oppr0 ltW.
    by rewrite divr_ge0// ltW.
  rewrite lerBlDl addrA -lerBlDr opprK.
  by rewrite lerD// (itvP xab).
rewrite le_eqVlt => /predU1P[FxBd|FxBd].
  have {}FxBd : F x = F (x + d').
    apply/eqP/negPn/negP; rewrite neq_lt => /orP[|].
      rewrite -FxBd ltNge => /negP; apply.
      rewrite ndF ?in_itv//=.
      by rewrite axd' xBd'b.
      by rewrite !(itvP xab).
      by rewrite gerBl ltW.
    rewrite ltNge => /negP; apply.
    rewrite ndF ?in_itv//=.
    by rewrite !(itvP xab).
    by rewrite xd'b andbT axDd'.
    by rewrite lerDl// ltW.
  have : (V `&` A) (x + d').
    split.
      apply: xdV.
      rewrite /ball_/=.
      by rewrite opprD addrA subrr add0r normrN gtr0_norm//.
    rewrite /A/=; split.
      rewrite in_itv/= xd'b andbT.
      by rewrite (ler_wpDr (ltW _))// (itvP xab).
    by rewrite -FxBd.
  rewrite VAx/=.
  by apply/eqP; rewrite eq_sym lt_eqF// ltrDl.
have [yE|] := eqVneq (F (x - d')) y.
  subst y.
  have : (V `&` A) (x - d').
    split.
      apply: xdV.
      rewrite /ball_/=.
      rewrite opprD addrA subrr add0r normrN ltr0_norm//.
      by rewrite oppr_lt0.
      by rewrite opprK.
    rewrite /A/=; split.
      by rewrite in_itv/= axd'/=.
    by rewrite yE.
  rewrite VAx/=.
  apply/eqP.
  by rewrite eq_sym gt_eqF// ltrBlDl ltrDr.
move=> Fxd'y.
have [yE|] := eqVneq (F (x + d')) y.
  subst y.
  have : (V `&` A) (x + d').
    split.
      apply: xdV.
      rewrite /ball_/=.
      by rewrite opprD addrA subrr add0r normrN gtr0_norm//.
    rewrite /A/=; split.
    by rewrite in_itv/= xd'b andbT (le_trans axd')//.
    by rewrite yE.
  rewrite VAx/=.
  apply/eqP.
  by rewrite eq_sym lt_eqF// ltrDl.
move=> yFxd'.
have [n /andP[xd'yn ynxd']] : exists n, F (x - d') < y_ n < F (x + d').
  pose k := Num.min ((F (x + d') - y) / 2) ((y - F (x - d')) / 2).
  have k0 : 0 < k.
    rewrite lt_min !divr_gt0//.
    rewrite subr_gt0.
    rewrite lt_neqAle eq_sym yFxd'/= ndF//.
    by apply: subset_itv_oo_cc.
    rewrite in_itv/= axDd'//=.
    by rewrite lerDl ltW.
    rewrite subr_gt0 lt_neqAle Fxd'y ndF//.
      by rewrite in_itv/= axd'//= (le_trans _ xd'b)//.
    by apply: subset_itv_oo_cc.
    by rewrite lerBlDl lerDr ltW.
  move/cvgrPdist_lt : y_cvg => /(_ _ k0)[n _]/(_ n (@leqnn n)).
  rewrite ltr_distlC => /andP[ykyn ynyk].
  exists n.
  apply/andP; split.
    rewrite (le_lt_trans _ ykyn)// /k.
    rewrite lerBrDl -lerBrDr.
    rewrite ge_min.
    apply/orP; right.
    rewrite ler_piMr//; last by rewrite ?invf_le1 ?ler1n//.
    rewrite subr_ge0 ndF//.
    by rewrite in_itv/= axd'/= (le_trans xd'xd').
    by rewrite in_itv/= !(itvP xab).
    by rewrite lerBlDl lerDr ltW.
  rewrite (lt_le_trans ynyk)// /k.
  rewrite -lerBrDl.
  rewrite ge_min.
  apply/orP; left.
  rewrite ler_piMr//; last by rewrite ?invf_le1 ?ler1n//.
  rewrite subr_ge0 ndF//.
  by rewrite in_itv/= !(itvP xab).
  rewrite in_itv/= xd'b andbT.
  by rewrite (le_trans axd')//.
  by rewrite lerDl ltW.
have H3 : {within `[x - d', x + d'], continuous F}.
  apply: continuous_subspaceW cF.
  by apply: subset_itv; rewrite bnd_simp//=.
have : Num.min (F (x - d')) (F (x + d')) <= y_ n <=
       Num.max (F (x - d')) (F (x + d')).
  by rewrite ge_min (ltW xd'yn)/= le_max (ltW ynxd') orbT.
move/IVT => /(_ xd'xd' H3)[x' x'xd Fx'yn].
have : x' \in V `&` A.
  rewrite inE.
  split.
    apply: xdV.
    apply/set_mem.
    rewrite -[X in _ \in X]/(ball _ _).
    rewrite ball_itv inE/=.
    apply: subset_itv x'xd; rewrite bnd_simp//=.
      by rewrite ltrD2l ltrN2//.
    by rewrite ltrD2l//.
  rewrite /A; split => //=.
  by apply: subset_itv x'xd; rewrite bnd_simp//=.
  rewrite Fx'yn.
  apply/y_K.
  by apply/imageT.
rewrite VAx inE/= => x'x.
subst x'.
move/eqP : Fx'yn.
apply/negP.
rewrite eq_sym.
exact: y_neq.
Qed.

Arguments open : clear implicits.
Arguments closed : clear implicits.
Arguments compact : clear implicits.
Arguments continuous_at : clear implicits.

(* lemma3 (converse) *)
(* NB: 1. In Hypothesis, "F is increasing" means nondecreasing or not?        *)
(*     2. In wlog step, "Gdelta-type" means Gdelta set?                       *)
(*        Then, can we obtain Z1 as (closure Z)?                              *)
(*     3. In Hypothesis and proof, when Gdelta-type doesn't means Gdelta set, *)
(*        "compact" means precompact, as compactness in `[a, b]?              *)
Lemma image_measure0_Lusin_nondecreasing (F : R -> R) :
  {within `[a, b], continuous F} ->
  (* increasing means nondecreasing or not? *)
  {in `[a, b] &, {homo F : x y / x <= y}} ->
  (forall Z : set R, Z `<=` `[a, b]%classic ->
      compact R Z ->
      mu Z = 0 ->
      mu (F @` Z) = 0) ->
  lusinN `[a, b] F.
Proof.
move=> cF ndF HZ.
(* Suppose on the contrary that F \notin (N) on `[a, b] *)
apply: contrapT.
(*Then there exists ... *)
move=> /existsNP[Z]/not_implyP[Zab/=] /not_implyP[mZ] /not_implyP[muZ0].
move=> /eqP; rewrite neq_lt ltNge measure_ge0/= => muFZ0.
have Zoo : (mu Z < +oo)%E.
  apply: (@le_lt_trans _ _ (mu `[a, b])); first exact: le_outer_measure.
  rewrite completed_lebesgue_measureE.
  by rewrite lebesgue_measure_itv/= lte_fin ab -EFinD ltry.
(* wlog (we should read Z1 as Z in paper) *)
have [U_ [ZU oU _ mZIU]] := lebesgue_measure_Gdelta_approx Zoo.
set Z1 := `]a, b[ `&` \bigcap_n U_ n.
have muZ10 : mu Z1 = 0.
  apply/eqP; rewrite -measure_le0/= -muZ0.
  rewrite completed_lebesgue_measureE.
  rewrite /lebesgue_measure/lebesgue_stieltjes_measure/measure_extension mZIU.
  apply: le_outer_measure.
  exact: subIsetr.
have gZ1 : Gdelta Z1.
 exists (fun n => `]a, b[ `&` U_ n).
    by move=> n; apply: openI.
  by rewrite bigcapIr.
have Z1ab : Z1 `<=` `]a, b[ by exact: subIsetl.
have mFZ1 : measurable (F @` Z1).
  exact: measurable_image_Gdelta_set_nondecreasing_fun Z1ab gZ1.
have FZ1oo : (mu (F @` Z1) < +oo)%E.
  apply: (@le_lt_trans _ _ (mu (F @` `]a, b[))).
    apply: le_outer_measure.
    exact: image_subset.
  apply: (@le_lt_trans _ _ (mu `[F a, F b])).
    apply: le_outer_measure.
    apply: continuous_nondecreasing_image_itvoo => //.
    by move=> ? ? ? ?; apply: ndF; exact: subset_itv_oo_cc.
  rewrite completed_lebesgue_measure_itv.
  by case: ifP => //; rewrite -EFinB ltry.
have ZabZ1 : Z `\ a `\ b `<=` Z1.
  rewrite subsetI; split.
  - rewrite -(setIidr Zab).
    rewrite -(setU1itv false) ?bnd_simp ?ltW//.
    rewrite setIUl setDUl.
    rewrite setIC -setIDA setDv setI0 set0U.
    rewrite -(setUitv1 true) ?bnd_simp ?ltW//.
    rewrite setIUl 2!setDUl -2!setIDA.
    rewrite -setIDA (setIC [set b]) -setIDA setDv setI0 setU0.
    exact: subIsetl.
  - apply: sub_bigcap => n _.
    apply: subset_trans (ZU n).
    rewrite setDDl.
    exact: subDsetl.
have FZ10 : (0 < mu (F @` Z1))%E.
  apply: (@lt_le_trans _ _ (mu (F @` (Z `\ a `\ b)))).
    by rewrite 2!measure_image_setD_set1.
  apply: le_outer_measure.
  exact: image_subset.
set e := fine (mu (F @` Z1)) / 2.
have e0 : 0 < e by rewrite divr_gt0 ?fine_gt0 ?FZ1oo ?FZ10.
set FZ1' := ((F @` Z1) `\` preimages_gt1 `[a, b] [set: R] F).
set e' := fine (mu FZ1') / 2.
have mpreF0 : mu ([set F x | x in Z1] `&` preimages_gt1 `[a, b] [set: R] F) = 0.
  apply: countable_lebesgue_measure0.
  apply: (@sub_countable _ _ _ (preimages_gt1 `[a, b] [set: R] F)).
    apply: subset_card_le.
    exact: subIsetr.
  exact: is_countable_preimages_gt1_nondecreasing_fun.
have e'0 : 0 < e'.
  rewrite /e' measureD//=.
  - exact: sub_caratheodory.
  - apply: sub_caratheodory.
    apply: countable_measurable => //.
    exact: is_countable_preimages_gt1_nondecreasing_fun.
  rewrite mpreF0 sube0.
  exact: e0.
have FZ1'oo : (mu FZ1' < +oo)%E.
  apply: le_lt_trans FZ1oo.
  apply: le_outer_measure.
  exact: subIsetl.
have mFZ1' : measurable FZ1'.
  apply: measurableI => //.
  apply: measurableC.
  apply: countable_measurable => //.
  exact: is_countable_preimages_gt1_nondecreasing_fun.
have [K [cK KFZ1' FZ1'Ke']] := lebesgue_regularity_inner mFZ1' FZ1'oo e'0.
set K1 := `[a, b] `&` F @^-1` K.
have K1K : F @` K1 = K.
  rewrite eqEsubset; split.
    apply: (subset_trans sub_image_setI).
    apply: subIset; right.
    exact: image_preimage_subset.
  move=> r Kr/=.
  pose L := `[a, b] `&` preimage F [set r].
  have L0 : L !=set0.
    have [] := @IVT _ _ _ _ r (ltW ab) cF.
      have Fab : F a <= F b.
        apply: ndF => //.
        - by rewrite boundl_in_itv bnd_simp ltW.
        - by rewrite boundr_in_itv bnd_simp ltW.
        - exact: ltW.
      rewrite minEle Fab.
      rewrite maxEle Fab.
      move: Kr=> /KFZ1'.
      case=> -[t [/= tab _] <-] _.
      rewrite 2?ndF//.
      - by rewrite bound_itvE// ltW.
      - exact: subset_itv_oo_cc.
      - by apply/ltW; move: tab; rewrite in_itv/= => /andP[].
      - exact: subset_itv_oo_cc.
      - by rewrite bound_itvE// ltW.
      - by apply/ltW; move: tab; rewrite in_itv/= => /andP[].
    by move=> x xab; rewrite /L; move <-; exists x.
  move: (L0) => [r'] /[dup] Lr'.
  rewrite /L/= => [[r'ab Fr'r]].
  exists r' => //.
  rewrite /K1/=; split => //.
  by rewrite Fr'r.
have : (0 < mu (F @` K1))%E.
  rewrite K1K.
  have := FZ1'Ke'.
  rewrite measureD//; first exact: compact_measurable.
  rewrite setIidr//.
  rewrite lteBlDl.
    rewrite ge0_fin_numE//.
    apply: le_lt_trans FZ1'oo.
    exact: le_outer_measure.
  rewrite -lteBlDr//.
  rewrite completed_lebesgue_measureE.
  apply: le_lt_trans.
  rewrite sube_ge0// /e EFinM fineK; first by rewrite ge0_fin_numE.
  rewrite muleC gee_pMl//.
  rewrite lee_fin invf_le1//.
  by rewrite -[leLHS](mulr1n 1) ler_nat.
apply/negP.
rewrite -leNgt.
rewrite measure_le0/=.
apply/eqP.
apply: HZ.
- exact: subIsetl.
- rewrite /K1 setIC -(setIid `[a, b]%classic) setICA.
  apply: compact_closedI; first exact: segment_compact.
  rewrite closed_setIS; first exact: itv_closed.
  apply: ((@continuous_closedP (subspace `[a, b]) _ F).1 cF).
  exact: compact_closed cK.
- apply/eqP; rewrite -measure_le0/=.
  rewrite -muZ10.
  apply: le_outer_measure.
  apply: (@subset_trans _ (`[a, b] `&` F @^-1` FZ1')).
    apply: setIS.
    exact: preimage_subset.
  rewrite /FZ1' setDE.
  rewrite [X in X `<=` _](_: _
    = Z1 `\` (F @^-1` preimages_gt1 `[a, b] [set: R] F)).
    rewrite eqEsubset; split.
    - move=> x/= [xab [[x' Z1x' Fx'Fx ]]].
      (* lemma? *)
      rewrite /preimages_gt1.
      rewrite not_andE not_notE orNp => /(_ Logic.I) sub1Fx.
      split => //.
      rewrite (sub1Fx x x')//.
      split => //.
      rewrite /=.
      apply: subset_itv_oo_cc.
      exact: Z1ab.
    - move=> x/= [Z1x].
      (* lemma? *)
      rewrite /preimages_gt1.
      rewrite not_andE not_notE orNp => /(_ Logic.I) sub1Fx.
      split => //.
        apply: subset_itv_oo_cc.
        exact: Z1ab.
      split => //.
      by exists x.
  exact: subDsetl.
Qed.

Section isolated_limit_point_lemmas.

Lemma continuous_preimage_limit_point (g : R -> R) (X: set R) (y : R) :
  {in X, continuous g} ->
  limit_point (g @` X) y ->
  forall x, x \in (g @^-1` [set y]) `&` X -> limit_point X x.
Proof.
move=> cg /limit_pointP[y_ [yY nyy cvg2y]] x.
rewrite inE/= => -[gxy Xx].
apply/limit_pointP.
have : forall n, exists z : R, z \in (g @^-1` [set y_ n]) `&` X.
  move=> n.
  have : range y_ (y_ n) by exists n.
  move/(yY (y_ n)) => [z Xz gzyn].
  by exists z; rewrite inE/=; split.
move/choice => [z_ zy].
exists z_; split.
    move => x1 [n _ <-]; have := zy n.
    by rewrite inE/= => -[].
  move=> n.
  apply/negP.
  move/eqP.
  move/(f_equal g).
  rewrite gxy.
  have := zy n.
  rewrite inE/= => -[-> _].
  move/eqP.
  apply/negP.
  exact: nyy.
move=> U [r /= r0 xrU].
have {}Xx : x \in X.
  by rewrite inE.
have nbhsgx : nbhs (g x) [set g x | x in U].
  admit.
have [r' /= r'0 r'gU] := cg x Xx (g @` U) nbhsgx.
have [rr /= rr0 Hrr] : nbhs y [set g x | x in U].
  exists r' => //.
  move=> t/=.
  admit.
have := cvg2y (g @` U).
rewrite -gxy.
move/(_ nbhsgx).
move=> [k _ Hk].
exists k => //.
move=> m /= km.
have [] := Hk m km.
Abort.

End isolated_limit_point_lemmas.

Lemma image_measure0_Lusin_nondecreasing_new (F : R -> R) :
  {within `[a, b], continuous F} ->
  (* increasing means nondecreasing or not? *)
  {in `[a, b] &, {homo F : x y / x <= y}} ->
  (forall Z : set R, Z `<=` `[a, b]%classic ->
      compact R Z ->
      isolated Z = set0 (* TODO: change compact to perfect set instead *) ->
      mu Z = 0 ->
      mu (F @` Z) = 0) ->
  lusinN `[a, b] F.
Proof.
move=> cF ndF HZ.
(* Suppose on the contrary that F \notin (N) on `[a, b] *)
apply: contrapT.
(*Then there exists ... *)
move=> /existsNP[Z]/not_implyP[Zab/=] /not_implyP[mZ] /not_implyP[muZ0].
move=> /eqP; rewrite neq_lt ltNge measure_ge0/= => muFZ0.
have Zoo : (mu Z < +oo)%E.
  apply: (@le_lt_trans _ _ (mu `[a, b])); first exact: le_outer_measure.
  rewrite completed_lebesgue_measureE.
  by rewrite lebesgue_measure_itv/= lte_fin ab -EFinD ltry.
(* wlog (we should read Z1 as Z in paper) *)
have [U_ [ZU oU _ mZIU]] := lebesgue_measure_Gdelta_approx Zoo.
set Z1 := `]a, b[ `&` \bigcap_n U_ n.
have muZ10 : mu Z1 = 0.
  apply/eqP; rewrite -measure_le0/= -muZ0.
  rewrite completed_lebesgue_measureE.
  rewrite /lebesgue_measure/lebesgue_stieltjes_measure/measure_extension mZIU.
  apply: le_outer_measure.
  exact: subIsetr.
have gZ1 : Gdelta Z1.
 exists (fun n => `]a, b[ `&` U_ n).
    by move=> n; apply: openI.
  by rewrite bigcapIr.
have Z1ab : Z1 `<=` `]a, b[ by exact: subIsetl.
have mFZ1 : measurable (F @` Z1).
  exact: measurable_image_Gdelta_set_nondecreasing_fun Z1ab gZ1.
have FZ1oo : (mu (F @` Z1) < +oo)%E.
  apply: (@le_lt_trans _ _ (mu (F @` `]a, b[))).
    apply: le_outer_measure.
    exact: image_subset.
  apply: (@le_lt_trans _ _ (mu `[F a, F b])).
    apply: le_outer_measure.
    apply: continuous_nondecreasing_image_itvoo => //.
    by move=> ? ? ? ?; apply: ndF; exact: subset_itv_oo_cc.
  rewrite completed_lebesgue_measure_itv.
  by case: ifP => //; rewrite -EFinB ltry.
have ZabZ1 : Z `\ a `\ b `<=` Z1.
  rewrite subsetI; split.
  - rewrite -(setIidr Zab).
    rewrite -(setU1itv false) ?bnd_simp ?ltW//.
    rewrite setIUl setDUl.
    rewrite setIC -setIDA setDv setI0 set0U.
    rewrite -(setUitv1 true) ?bnd_simp ?ltW//.
    rewrite setIUl 2!setDUl -2!setIDA.
    rewrite -setIDA (setIC [set b]) -setIDA setDv setI0 setU0.
    exact: subIsetl.
  - apply: sub_bigcap => n _.
    apply: subset_trans (ZU n).
    rewrite setDDl.
    exact: subDsetl.
have FZ10 : (0 < mu (F @` Z1))%E.
  apply: (@lt_le_trans _ _ (mu (F @` (Z `\ a `\ b)))).
    by rewrite 2!measure_image_setD_set1.
  apply: le_outer_measure.
  exact: image_subset.
set e := fine (mu (F @` Z1)) / 2.
have e0 : 0 < e by rewrite divr_gt0 ?fine_gt0 ?FZ1oo ?FZ10.
set FZ1' := ((F @` Z1) `\` preimages_gt1 `[a, b] [set: R] F).
set e' := fine (mu FZ1') / 2.
have mpreF0 : mu ([set F x | x in Z1] `&` preimages_gt1 `[a, b] [set: R] F) = 0.
  apply: countable_lebesgue_measure0.
  apply: (@sub_countable _ _ _ (preimages_gt1 `[a, b] [set: R] F)).
    apply: subset_card_le.
    exact: subIsetr.
  exact: is_countable_preimages_gt1_nondecreasing_fun.
have e'0 : 0 < e'.
  rewrite /e' measureD//=.
  - exact: sub_caratheodory.
  - apply: sub_caratheodory.
    apply: countable_measurable => //.
    exact: is_countable_preimages_gt1_nondecreasing_fun.
  rewrite mpreF0 sube0.
  exact: e0.
have FZ1'oo : (mu FZ1' < +oo)%E.
  apply: le_lt_trans FZ1oo.
  apply: le_outer_measure.
  exact: subIsetl.
have mFZ1' : measurable FZ1'.
  apply: measurableI => //.
  apply: measurableC.
  apply: countable_measurable => //.
  exact: is_countable_preimages_gt1_nondecreasing_fun.
have [K [cK KFZ1' FZ1'Ke']] := lebesgue_regularity_inner mFZ1' FZ1'oo e'0.
wlog : K cK KFZ1' FZ1'Ke' / isolated K = set0.
  move=> wlg.
  have : (mu K < +oo)%E.
    rewrite (le_lt_trans _ FZ1'oo)//.
    by rewrite le_outer_measure.
  move/(perfect_set_rm cK) => [K0 [K0K cK0 isoK0 mK0]].
  apply: (wlg K0) => //.
  by apply: subset_trans KFZ1'.
  rewrite (le_lt_trans _ FZ1'Ke')//.
  rewrite measureD//.
    by apply: compact_measurable.
  rewrite [in leRHS]measureD//.
    by apply: compact_measurable.
  rewrite leeD//.
  rewrite leeN2.
  rewrite setIidr//.
  rewrite setIidr//.
    by apply: (subset_trans K0K).
  by rewrite [leRHS]mK0//.
move=> isoK0.
set K1 := `[a, b] `&` F @^-1` K.
have K1K : F @` K1 = K.
  rewrite eqEsubset; split.
    apply: (subset_trans sub_image_setI).
    apply: subIset; right.
    exact: image_preimage_subset.
  move=> r Kr/=.
  pose L := `[a, b] `&` preimage F [set r].
  have L0 : L !=set0.
    have [] := @IVT _ _ _ _ r (ltW ab) cF.
      have Fab : F a <= F b.
        apply: ndF => //.
        - by rewrite boundl_in_itv bnd_simp ltW.
        - by rewrite boundr_in_itv bnd_simp ltW.
        - exact: ltW.
      rewrite minEle Fab.
      rewrite maxEle Fab.
      move: Kr=> /KFZ1'.
      case=> -[t [/= tab _] <-] _.
      rewrite 2?ndF//.
      - by rewrite bound_itvE// ltW.
      - exact: subset_itv_oo_cc.
      - by apply/ltW; move: tab; rewrite in_itv/= => /andP[].
      - exact: subset_itv_oo_cc.
      - by rewrite bound_itvE// ltW.
      - by apply/ltW; move: tab; rewrite in_itv/= => /andP[].
    by move=> x xab; rewrite /L; move <-; exists x.
  move: (L0) => [r'] /[dup] Lr'.
  rewrite /L/= => [[r'ab Fr'r]].
  exists r' => //.
  rewrite /K1/=; split => //.
  by rewrite Fr'r.
have : (0 < mu (F @` K1))%E.
  rewrite K1K.
  have := FZ1'Ke'.
  rewrite measureD//; first exact: compact_measurable.
  rewrite setIidr//.
  rewrite lteBlDl.
    rewrite ge0_fin_numE//.
    apply: le_lt_trans FZ1'oo.
    exact: le_outer_measure.
  rewrite -lteBlDr//.
  rewrite completed_lebesgue_measureE.
  apply: le_lt_trans.
  rewrite sube_ge0// /e EFinM fineK; first by rewrite ge0_fin_numE.
  rewrite muleC gee_pMl//.
  rewrite lee_fin invf_le1//.
  by rewrite -[leLHS](mulr1n 1) ler_nat.
apply/negP.
rewrite -leNgt.
rewrite measure_le0/=.
apply/eqP.
apply: HZ.
- exact: subIsetl.
- rewrite /K1 setIC -(setIid `[a, b]%classic) setICA.
  apply: compact_closedI; first exact: segment_compact.
  rewrite closed_setIS; first exact: itv_closed.
  apply: ((@continuous_closedP (subspace `[a, b]) _ F).1 cF).
  exact: compact_closed cK.
- by apply: nondecreasing_cont_isolated => //.
- apply/eqP; rewrite -measure_le0/=.
  rewrite -muZ10.
  apply: le_outer_measure.
  apply: (@subset_trans _ (`[a, b] `&` F @^-1` FZ1')).
    apply: setIS.
    exact: preimage_subset.
  rewrite /FZ1' setDE.
  rewrite [X in X `<=` _](_: _
    = Z1 `\` (F @^-1` preimages_gt1 `[a, b] [set: R] F)).
    rewrite eqEsubset; split.
    - move=> x/= [xab [[x' Z1x' Fx'Fx ]]].
      (* lemma? *)
      rewrite /preimages_gt1.
      rewrite not_andE not_notE orNp => /(_ Logic.I) sub1Fx.
      split => //.
      rewrite (sub1Fx x x')//.
      split => //.
      rewrite /=.
      apply: subset_itv_oo_cc.
      exact: Z1ab.
    - move=> x/= [Z1x].
      (* lemma? *)
      rewrite /preimages_gt1.
      rewrite not_andE not_notE orNp => /(_ Logic.I) sub1Fx.
      split => //.
        apply: subset_itv_oo_cc.
        exact: Z1ab.
      split => //.
      by exists x.
  exact: subDsetl.
Qed.

End main_lemma.

End lemma3.
