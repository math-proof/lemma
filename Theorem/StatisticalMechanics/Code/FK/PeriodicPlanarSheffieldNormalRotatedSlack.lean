/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

theorem exists_currentSuccessorMarginIndex
    (horizontal vertical : Nat -> Nat)
    (hhorizontal : Tendsto horizontal atTop atTop)
    (hvertical : Tendsto vertical atTop atTop)
    (horizontalRequirement verticalRequirement : Fin 8 -> Int) :
    exists k,
      (forall i, horizontalRequirement i <= horizontal k) /\
      (forall i, horizontalRequirement i <= horizontal (k + 1)) /\
      (forall i, verticalRequirement i <= vertical k) := by
  let horizontalTarget : Nat :=
    ∑ i : Fin 8, (horizontalRequirement i).natAbs
  let verticalTarget : Nat :=
    ∑ i : Fin 8, (verticalRequirement i).natAbs
  have hHorizontal : ∀ᶠ k in atTop, horizontalTarget <= horizontal k :=
    hhorizontal (eventually_ge_atTop horizontalTarget)
  have hVertical : ∀ᶠ k in atTop, verticalTarget <= vertical k :=
    hvertical (eventually_ge_atTop verticalTarget)
  obtain ⟨horizontalIndex, hHorizontalIndex⟩ :=
    eventually_atTop.1 hHorizontal
  obtain ⟨verticalIndex, hVerticalIndex⟩ :=
    eventually_atTop.1 hVertical
  let k := max horizontalIndex verticalIndex
  have hkHorizontal := hHorizontalIndex k (Nat.le_max_left _ _)
  have hkHorizontalSucc := hHorizontalIndex (k + 1)
    ((Nat.le_max_left horizontalIndex verticalIndex).trans
      (Nat.le_add_right k 1))
  have hkVertical := hVerticalIndex k (Nat.le_max_right _ _)
  have hHorizontalTerm (i : Fin 8) :
      (horizontalRequirement i).natAbs <= horizontalTarget := by
    dsimp only [horizontalTarget]
    exact Finset.single_le_sum
      (f := fun j : Fin 8 => (horizontalRequirement j).natAbs)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hVerticalTerm (i : Fin 8) :
      (verticalRequirement i).natAbs <= verticalTarget := by
    dsimp only [verticalTarget]
    exact Finset.single_le_sum
      (f := fun j : Fin 8 => (verticalRequirement j).natAbs)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  refine ⟨k, ?_, ?_, ?_⟩
  · intro i
    exact Int.le_natAbs.trans (by
      exact_mod_cast (hHorizontalTerm i).trans hkHorizontal)
  · intro i
    exact Int.le_natAbs.trans (by
      exact_mod_cast (hHorizontalTerm i).trans hkHorizontalSucc)
  · intro i
    exact Int.le_natAbs.trans (by
      exact_mod_cast (hVerticalTerm i).trans hkVertical)

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

omit [Countable V] in

theorem PeriodicPlaneEmbedding.orbitBoxCoordinateBound_mono
    (E : PeriodicPlaneEmbedding P) {n m : Nat} (hnm : n <= m)
    (i : Fin 2) :
    E.orbitBoxCoordinateBound n i <= E.orbitBoxCoordinateBound m i := by
  classical
  unfold PeriodicPlaneEmbedding.orbitBoxCoordinateBound
  exact Finset.sup'_mono (fun v => |E.vertexCoord v i|)
    (fun _ hv => P.orbitBox_mono hnm hv)
    ⟨P.root, P.orbitBox_mono (Nat.zero_le n)
      P.root_mem_orbitBox_zero⟩

omit [Countable V] in

theorem PeriodicPlaneEmbedding.connectorMarginRequirement_mono
    (E : PeriodicPlaneEmbedding P) {radius radius' : Nat}
    (h : radius <= radius') :
    E.connectorMarginRequirement radius <=
      E.connectorMarginRequirement radius' := by
  unfold PeriodicPlaneEmbedding.connectorMarginRequirement
  apply Nat.ceil_mono
  apply max_le_max
  · apply E.orbitBoxCoordinateBound_mono
    exact P.bufferedRadius_strictMono.monotone h
  · apply E.orbitBoxCoordinateBound_mono
    exact P.bufferedRadius_strictMono.monotone h


theorem PeriodicPlaneEmbedding.axisSwap_horizontalCrossingEvent_subset_verticalCrossingEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisSwap.horizontalCrossingEvent a b c d ⊆
      E.verticalCrossingEvent c d a b := by
  intro omega homega
  change E.axisSwap.rectRestrict a b c d omega ∈
    E.axisSwap.finiteHorizontalCrossing a b c d at homega
  obtain ⟨x, y, hxLeft, hyRight, hxy⟩ := homega
  have hx' : x.1 ∈ E.rectVertices c d a b := by
    exact ⟨by simpa using x.2.2.2.1, by simpa using x.2.2.2.2,
      by simpa using x.2.1, by simpa using x.2.2.1⟩
  have hy' : y.1 ∈ E.rectVertices c d a b := by
    exact ⟨by simpa using y.2.2.2.1, by simpa using y.2.2.2.2,
      by simpa using y.2.1, by simpa using y.2.2.1⟩
  have hxBottom : E.rectBottomBoundary c d a b ⟨x.1, hx'⟩ := by
    obtain ⟨z, hxz, hz⟩ := hxLeft
    refine ⟨z, hxz, ?_⟩
    simpa using hz
  have hyTop : E.rectTopBoundary c d a b ⟨y.1, hy'⟩ := by
    obtain ⟨z, hyz, hz⟩ := hyRight
    refine ⟨z, hyz, ?_⟩
    simpa using hz
  rw [E.axisSwap.openSub_rectRestrict_eq_induce] at hxy
  obtain ⟨p⟩ := hxy
  let pAmbient : (P.openSubgraph omega).Walk x.1 y.1 :=
    p.map (SimpleGraph.Embedding.induce
      (E.axisSwap.rectVertices a b c d)).toHom
  have hpAmbient : ∀ v ∈ pAmbient.support,
      v ∈ E.rectVertices c d a b := by
    intro v hv
    have hv' : v ∈
        (p.map (SimpleGraph.Embedding.induce
          (E.axisSwap.rectVertices a b c d)).toHom).support := hv
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hv'
    obtain ⟨w, _hw, rfl⟩ := hv'
    exact ⟨by simpa using w.2.2.2.1, by simpa using w.2.2.2.2,
      by simpa using w.2.1, by simpa using w.2.2.1⟩
  have hreach :
      ((P.openSubgraph omega).induce (E.rectVertices c d a b)).Reachable
        ⟨x.1, hx'⟩ ⟨y.1, hy'⟩ :=
    ⟨pAmbient.induce (E.rectVertices c d a b) hpAmbient⟩
  change E.rectRestrict c d a b omega ∈ E.finiteVerticalCrossing c d a b
  refine ⟨⟨x.1, hx'⟩, ⟨y.1, hy'⟩, hxBottom, hyTop, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hreach


theorem PeriodicPlaneEmbedding.axisSwap_crossingMax_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (aH bH cH dH aV bV cV dV : Nat -> Real)
    (hlimit : Tendsto (fun n => max
      (mu.real (E.axisSwap.horizontalCrossingEvent
        (aH n) (bH n) (cH n) (dH n)))
      (mu.real (E.axisSwap.verticalCrossingEvent
        (aV n) (bV n) (cV n) (dV n)))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.verticalCrossingEvent
        (cH n) (dH n) (aH n) (bH n)))
      (mu.real (E.horizontalCrossingEvent
        (cV n) (dV n) (aV n) (bV n)))) atTop (nhds 1) := by
  apply hlimit.squeeze tendsto_const_nhds
  · intro n
    apply max_le_max
    · exact measureReal_mono
        (E.axisSwap_horizontalCrossingEvent_subset_verticalCrossingEvent
          (aH n) (bH n) (cH n) (dH n))
    · exact measureReal_mono
        (E.axisSwap_verticalCrossingEvent_subset_horizontalCrossingEvent
          (aV n) (bV n) (cV n) (dV n))
  · intro n
    exact max_le measureReal_le_one measureReal_le_one

omit [Countable V] [Countable W] in


theorem PairedAlignedConnectorSlack.of_le
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {radius radius' k : Nat} (h : radius <= radius')
    (slack : PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius' k) :
    PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius k := by
  have hprimal := E.connectorMarginRequirement_mono h
  have hdual := Edual.connectorMarginRequirement_mono h
  have hprimalInt : (E.connectorMarginRequirement radius : Int) <=
      E.connectorMarginRequirement radius' := by
    exact_mod_cast hprimal
  have hdualInt : (Edual.connectorMarginRequirement radius : Int) <=
      Edual.connectorMarginRequirement radius' := by
    exact_mod_cast hdual
  exact {
    primalLeft := hprimalInt.trans slack.primalLeft
    primalRight := by
      have := slack.primalRight
      omega
    primalBottom := hprimalInt.trans slack.primalBottom
    primalTop := by
      have := slack.primalTop
      omega
    dualLeft := hdualInt.trans slack.dualLeft
    dualRight := by
      have := slack.dualRight
      omega
    dualBottom := hdualInt.trans slack.dualBottom
    dualTop := by
      have := slack.dualTop
      omega }


theorem tendsto_two_max_one_fixedBranches_subsequence
    (H0 V1 V0 H1 : Nat -> Real)
    (hnormal : Tendsto (fun n => max (H0 n) (V1 n))
      atTop (nhds 1))
    (hrotated : Tendsto (fun n => max (V0 n) (H1 n))
      atTop (nhds 1)) :
    (exists phi : Nat -> Nat, StrictMono phi /\
      Tendsto (fun n => H0 (phi n)) atTop (nhds 1) /\
      Tendsto (fun n => V0 (phi n)) atTop (nhds 1)) \/
    (exists phi : Nat -> Nat, StrictMono phi /\
      Tendsto (fun n => H0 (phi n)) atTop (nhds 1) /\
      Tendsto (fun n => H1 (phi n)) atTop (nhds 1)) \/
    (exists phi : Nat -> Nat, StrictMono phi /\
      Tendsto (fun n => V1 (phi n)) atTop (nhds 1) /\
      Tendsto (fun n => V0 (phi n)) atTop (nhds 1)) \/
    (exists phi : Nat -> Nat, StrictMono phi /\
      Tendsto (fun n => V1 (phi n)) atTop (nhds 1) /\
      Tendsto (fun n => H1 (phi n)) atTop (nhds 1)) := by
  rcases tendsto_max_one_fixedBranch_subsequence H0 V1 hnormal with
    ⟨phi, hphi, _hphiBranch, hH0⟩ |
    ⟨phi, hphi, _hphiBranch, hV1⟩
  · have hrotated' := hrotated.comp hphi.tendsto_atTop
    rcases tendsto_max_one_fixedBranch_subsequence
        (fun n => V0 (phi n)) (fun n => H1 (phi n)) hrotated' with
      ⟨psi, hpsi, _hpsiBranch, hV0⟩ |
      ⟨psi, hpsi, _hpsiBranch, hH1⟩
    · left
      refine ⟨phi ∘ psi, hphi.comp hpsi, ?_, ?_⟩
      · simpa only [Function.comp_apply] using
          hH0.comp hpsi.tendsto_atTop
      · simpa only [Function.comp_apply] using hV0
    · right
      left
      refine ⟨phi ∘ psi, hphi.comp hpsi, ?_, ?_⟩
      · simpa only [Function.comp_apply] using
          hH0.comp hpsi.tendsto_atTop
      · simpa only [Function.comp_apply] using hH1
  · have hrotated' := hrotated.comp hphi.tendsto_atTop
    rcases tendsto_max_one_fixedBranch_subsequence
        (fun n => V0 (phi n)) (fun n => H1 (phi n)) hrotated' with
      ⟨psi, hpsi, _hpsiBranch, hV0⟩ |
      ⟨psi, hpsi, _hpsiBranch, hH1⟩
    · right
      right
      left
      refine ⟨phi ∘ psi, hphi.comp hpsi, ?_, ?_⟩
      · simpa only [Function.comp_apply] using
          hV1.comp hpsi.tendsto_atTop
      · simpa only [Function.comp_apply] using hV0
    · right
      right
      right
      refine ⟨phi ∘ psi, hphi.comp hpsi, ?_, ?_⟩
      · simpa only [Function.comp_apply] using
          hV1.comp hpsi.tendsto_atTop
      · simpa only [Function.comp_apply] using hH1


theorem exists_pairedAlignedNormalRotatedConnectorSlack
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (radius radiusRotated : Nat) :
    exists k,
      PairedAlignedConnectorSlack E Edual family familyDual schedule
        radius k /\
      PairedAlignedConnectorSlack E.axisSwap Edual.axisSwap
        family.axisSwap familyDual.axisSwap schedule.axisSwap
        radiusRotated k := by
  let MP : Int := E.connectorMarginRequirement radius
  let MD : Int := Edual.connectorMarginRequirement radius
  let MPR : Int := E.axisSwap.connectorMarginRequirement radiusRotated
  let MDR : Int :=
    Edual.axisSwap.connectorMarginRequirement radiusRotated
  let H : Fin 8 -> Int := ![
    MP - family.baseLeft 0,
    family.baseRight 0 + MP,
    MD - familyDual.baseLeft 0,
    familyDual.baseRight 0 + MD,
    MPR - family.baseLeft 0,
    family.baseRight 0 + MPR,
    MDR - familyDual.baseLeft 0,
    familyDual.baseRight 0 + MDR]
  let Vreq : Fin 8 -> Int := ![
    MP - family.baseBottom 1,
    family.baseTop 1 + MP,
    MD - familyDual.baseBottom 1,
    familyDual.baseTop 1 + MD,
    MPR - family.baseBottom 1,
    family.baseTop 1 + MPR,
    MDR - familyDual.baseBottom 1,
    familyDual.baseTop 1 + MDR]
  obtain ⟨k, hH, hHSucc, hV⟩ :=
    exists_currentSuccessorMarginIndex schedule.horizontal schedule.vertical
      schedule.horizontal_tendsto schedule.vertical_tendsto H Vreq
  have hH0 := hH (0 : Fin 8)
  have hH1 := hH (1 : Fin 8)
  have hH2 := hH (2 : Fin 8)
  have hH3 := hH (3 : Fin 8)
  have hHS4 := hHSucc (4 : Fin 8)
  have hHS5 := hHSucc (5 : Fin 8)
  have hHS6 := hHSucc (6 : Fin 8)
  have hHS7 := hHSucc (7 : Fin 8)
  have hV0 := hV (0 : Fin 8)
  have hV1 := hV (1 : Fin 8)
  have hV2 := hV (2 : Fin 8)
  have hV3 := hV (3 : Fin 8)
  have hV4 := hV (4 : Fin 8)
  have hV5 := hV (5 : Fin 8)
  have hV6 := hV (6 : Fin 8)
  have hV7 := hV (7 : Fin 8)
  simp [H, MP, MD, MPR, MDR] at hH0 hH1 hH2 hH3
  simp [H, MP, MD, MPR, MDR] at hHS4 hHS5 hHS6 hHS7
  simp [Vreq, MP, MD, MPR, MDR] at hV0 hV1 hV2 hV3
  simp [Vreq, MP, MD, MPR, MDR] at hV4 hV5 hV6 hV7
  refine ⟨k, {
    primalLeft := by omega
    primalRight := by omega
    primalBottom := by omega
    primalTop := by omega
    dualLeft := by omega
    dualRight := by omega
    dualBottom := by omega
    dualTop := by omega }, ?_⟩
  refine {
    primalLeft := ?_
    primalRight := ?_
    primalBottom := ?_
    primalTop := ?_
    dualLeft := ?_
    dualRight := ?_
    dualBottom := ?_
    dualTop := ?_ }
  · change E.axisSwap.connectorMarginRequirement radiusRotated <=
      family.baseBottom 1 + schedule.vertical k
    omega
  · change family.baseTop 1 - schedule.vertical k +
      E.axisSwap.connectorMarginRequirement radiusRotated <= 0
    omega
  · change E.axisSwap.connectorMarginRequirement radiusRotated <=
      family.baseLeft 0 + schedule.horizontal (k + 1)
    omega
  · change family.baseRight 0 - schedule.horizontal (k + 1) +
      E.axisSwap.connectorMarginRequirement radiusRotated <= 0
    omega
  · change Edual.axisSwap.connectorMarginRequirement radiusRotated <=
      familyDual.baseBottom 1 + schedule.vertical k
    omega
  · change familyDual.baseTop 1 - schedule.vertical k +
      Edual.axisSwap.connectorMarginRequirement radiusRotated <= 0
    omega
  · change Edual.axisSwap.connectorMarginRequirement radiusRotated <=
      familyDual.baseLeft 0 + schedule.horizontal (k + 1)
    omega
  · change familyDual.baseRight 0 - schedule.horizontal (k + 1) +
      Edual.axisSwap.connectorMarginRequirement radiusRotated <= 0
    omega


theorem PeriodicPlaneEmbedding.exists_uniformOrbitBoxMixedRadius_alignedExact_dualLimit
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (p pDual : Nat -> Real)
    (family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n))
    (familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual
        (Pdual.orbitBox n) (pDual n))
    (schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (hpDual_le : forall n, pDual n <= 1) :
    exists radius : Nat -> Nat,
      forall (k extentX extentY : Nat -> Nat)
        (data : forall n, AlignedExactExtentPairedMixedBoundaryScores
          E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
          (p n) (pDual n) (family n) (familyDual n) (schedule n)
          (k n) (extentX n) (extentY n)),
        (forall n, PairedAlignedConnectorSlack E Edual
          (family n) (familyDual n) (schedule n)
          (max (radius n) n) (k n)) ->
        Tendsto (fun n => max
          (muDual.real (Edual.horizontalCrossingEvent
            0 (extentX n) 0 (extentY n)))
          (muDual.real (Edual.verticalCrossingEvent
            (data n).raw.data.wideLeft (data n).raw.data.wideRight
            0 (extentY n)))) atTop (nhds 1) := by
  let template : Nat -> Finset W := fun n => Pdual.orbitBox n
  have hexists :
      muDual {eta | Pdual.HasInfiniteCluster eta} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- huniqueDual]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      muDual.real (Pdual.setHitsInfinite (template n : Set W)))
      atTop (nhds 1) := by
    simpa only [template, PeriodicGraph.setHitsInfinite,
      PeriodicGraph.orbitBoxHitsInfinite] using
      Pdual.orbitBoxHitsInfinite_real_tendsto_one muDual hexists
  obtain ⟨radius, hcross⟩ :=
    Edual.exists_uniformTemplate_mixedBoundaryScores_crossing_max_tendsto_one
      muDual hFKGDual hTIDual huniqueDual template htemplateHit
  refine ⟨radius, ?_⟩
  intro k extentX extentY data slack
  apply hcross
      (fun n => (data n).raw.data.widthDual)
      (fun n => (data n).raw.data.heightDual)
      (fun n => (data n).raw.data.widthDual_pos)
      (fun n => (data n).raw.data.heightDual_pos)
      (fun n => (data n).raw.data.baseDual)
      (fun _ => 0) (fun n => (extentX n : Real))
      (fun _ => 0) (fun n => (extentY n : Real))
      (fun n => (data n).raw.data.wideLeft)
      (fun n => (data n).raw.data.wideRight)
      (fun _ => 0) (fun n => (extentY n : Real)) pDual hpDual hpDual_le
  · intro n
    exact (data n).raw.data.wideLeft_le
  · intro n
    simpa [(data n).raw.narrowRight_eq] using
      (data n).raw.data.narrowRight_le
  · intro n
    exact le_rfl
  · intro n
    exact le_rfl
  · intro n gridVertex vertex hvertex
    apply (data n).dualConnector_subset_narrow (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := by
      simpa only [template, Finset.mem_coe, Finset.mem_image] using hvertex
    refine ⟨sourceVertex, Pdual.orbitBox_mono ?_ hsourceVertex, rfl⟩
    exact (Nat.le_max_right (radius n) n).trans
      (Pdual.id_le_bufferedRadius (max (radius n) n))
  · intro n gridVertex vertex hvertex
    apply (data n).dualConnector_subset_narrow (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, Pdual.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply Pdual.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n gridVertex vertex hvertex
    rw [<- (data n).raw.shortTop_eq]
    apply (data n).dualConnector_subset_wide (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, Pdual.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply Pdual.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n i
    simpa [template, (data n).raw.shortTop_eq] using
      le_of_lt ((data n).raw.data.dual_bottom i)
  · intro n i
    simpa [template, (data n).raw.shortTop_eq] using
      le_of_lt ((data n).raw.data.dual_top i)
  · intro n j
    simpa [template, (data n).raw.narrowRight_eq,
      (data n).raw.tallTop_eq] using
      le_of_lt ((data n).raw.data.dual_left j)
  · intro n j
    simpa [template, (data n).raw.narrowRight_eq,
      (data n).raw.tallTop_eq] using
      le_of_lt ((data n).raw.data.dual_right j)


end StatMech.FK.PeriodicPlanar
