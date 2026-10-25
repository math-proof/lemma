/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldNormalRotatedSlack.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem NormalTwoRotatedEndpointLimitData.normalWide_real_span_eq
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    (data : NormalTwoRotatedEndpointLimitData E Edual mu muDual)
    (n : Nat) :
    (data.level n).normal.raw.data.wideRight -
        (data.level n).normal.raw.data.wideLeft =
      (data.level n).rotatedHorizontalY := by
  rw [(data.level n).normal.raw.wideLeft_eq,
    (data.level n).normal.raw.wideRight_eq]
  exact_mod_cast (data.level n).normalSpan_eq


theorem NormalTwoRotatedEndpointLimitData.rotatedHorizontalWide_real_span_eq
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    (data : NormalTwoRotatedEndpointLimitData E Edual mu muDual)
    (n : Nat) :
    (data.level n).rotatedHorizontal.raw.data.wideRight -
        (data.level n).rotatedHorizontal.raw.data.wideLeft =
      (data.level n).normalY := by
  have hspan := (data.level n).rotatedHorizontalSpan_eq
  rw [(data.level n).rotatedHorizontal.raw.wideLeft_eq,
    (data.level n).rotatedHorizontal.raw.wideRight_eq]
  exact_mod_cast hspan


theorem NormalTwoRotatedEndpointLimitData.dualRotatedVerticalOriginalLimit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    (data : NormalTwoRotatedEndpointLimitData E Edual mu muDual) :
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        0 (data.level n).normalX 0 (data.level n).normalY))
      (muDual.real (Edual.horizontalCrossingEvent
        0 (data.level n).normalX
        (data.rotatedVerticalLevel n).raw.data.wideLeft
        (data.rotatedVerticalLevel n).raw.data.wideRight)))
      atTop (nhds 1) := by
  exact Edual.axisSwap_crossingMax_tendsto_one muDual
    (fun _ => 0) (fun n => (data.level n).normalY)
    (fun _ => 0) (fun n => (data.level n).normalX)
    (fun n => (data.rotatedVerticalLevel n).raw.data.wideLeft)
    (fun n => (data.rotatedVerticalLevel n).raw.data.wideRight)
    (fun _ => 0) (fun n => (data.level n).normalX)
    data.dualRotatedVerticalLimit


theorem NormalTwoRotatedEndpointLimitData.dualRotatedHorizontalOriginalLimit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    (data : NormalTwoRotatedEndpointLimitData E Edual mu muDual) :
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        0 (data.level n).rotatedHorizontalY 0
        (data.level n).rotatedHorizontalX))
      (muDual.real (Edual.horizontalCrossingEvent
        0 (data.level n).rotatedHorizontalY
        (data.rotatedHorizontalLevel n).raw.data.wideLeft
        (data.rotatedHorizontalLevel n).raw.data.wideRight)))
      atTop (nhds 1) := by
  exact Edual.axisSwap_crossingMax_tendsto_one muDual
    (fun _ => 0) (fun n => (data.level n).rotatedHorizontalX)
    (fun _ => 0) (fun n => (data.level n).rotatedHorizontalY)
    (fun n => (data.rotatedHorizontalLevel n).raw.data.wideLeft)
    (fun n => (data.rotatedHorizontalLevel n).raw.data.wideRight)
    (fun _ => 0) (fun n => (data.level n).rotatedHorizontalY)
    data.dualRotatedHorizontalLimit


theorem nonempty_normalTwoRotatedEndpointLimitData_of_unique
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
    Nonempty (NormalTwoRotatedEndpointLimitData E Edual mu muDual) := by
  obtain ⟨score, scoreDual, family, familyDual,
      hscore, hscore_le, hscoreDual, hscoreDual_le⟩ :=
    exists_pairedCofinalNormalBoundaryBandFamilies_bounded
      E Edual mu muDual hFKG hTI hunique
        hFKGDual hTIDual huniqueDual
  let schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0) := fun n =>
    Classical.choice (exists_pairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0))
  let familyRotated : forall n,
      E.axisSwap.NormalBoundaryBandFamily mu
        (P.axisSwap.orbitBox n) (score n) := fun n => by
    simpa only [P.axisSwap_orbitBox] using (family n).axisSwap
  let familyDualRotated : forall n,
      Edual.axisSwap.NormalBoundaryBandFamily muDual
        (Pdual.axisSwap.orbitBox n) (scoreDual n) := fun n => by
    simpa only [Pdual.axisSwap_orbitBox] using (familyDual n).axisSwap
  let scheduleRotated : forall n,
      PairedAlignedMarginSchedule E.axisSwap Edual.axisSwap
        (familyRotated n) (familyDualRotated n)
        (fun _ => 0) (fun _ => 0) := fun n => by
    convert (schedule n).axisSwap using 1
    · exact P.axisSwap_orbitBox n
    · exact Pdual.axisSwap_orbitBox n
    all_goals exact cast_heq _ _
  obtain ⟨radiusNormal, hnormal⟩ :=
    E.exists_uniformOrbitBoxMixedRadius_alignedExact_primalLimit
      Edual mu muDual hFKG hTI hunique score scoreDual family familyDual
      schedule hscore hscore_le
  obtain ⟨radiusDualRotated, hrotatedDual⟩ :=
    E.axisSwap.exists_uniformOrbitBoxMixedRadius_alignedExact_dualLimit
      Edual.axisSwap mu muDual hFKGDual
      (Pdual.axisSwap_isTranslationInvariant muDual hTIDual) huniqueDual
      score scoreDual familyRotated familyDualRotated scheduleRotated
      hscoreDual hscoreDual_le
  let normalRadius : Nat -> Nat := fun n => max (radiusNormal n) n
  let rotatedRadius : Nat -> Nat := fun n =>
    max (radiusDualRotated n) n
  have hslack (n : Nat) :=
    exists_pairedAlignedNormalRotatedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n)
      (normalRadius n) (rotatedRadius n)
  let index : Nat -> Nat := fun n => Classical.choose (hslack n)
  let normalSlack : forall n, PairedAlignedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n)
      (max (radiusNormal n) n) (index n) := fun n =>
    (Classical.choose_spec (hslack n)).1
  let rotatedSlack : forall n,
      PairedAlignedConnectorSlack E.axisSwap Edual.axisSwap
        (familyRotated n) (familyDualRotated n) (scheduleRotated n)
        (max (radiusDualRotated n) n) (index n) := fun n => by
    convert (Classical.choose_spec (hslack n)).2 using 1
    · exact P.axisSwap_orbitBox n
    · exact Pdual.axisSwap_orbitBox n
    all_goals exact cast_heq _ _
  let level : forall n,
      AlignedNormalTwoRotatedEndpointPairedMixedBoundaryScores
        E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
        (score n) (scoreDual n) (family n) (familyDual n)
        (schedule n) (index n) := fun n => Classical.choice
    (nonempty_alignedNormalTwoRotatedEndpointPairedMixedBoundaryScores
      E Edual mu muDual hTI hTIDual (family n) (familyDual n)
      (schedule n) (index n))
  let rotatedVerticalLevel : forall n,
      AlignedExactExtentPairedMixedBoundaryScores
        E.axisSwap Edual.axisSwap mu muDual
        (P.axisSwap.orbitBox n) (Pdual.axisSwap.orbitBox n)
        (score n) (scoreDual n) (familyRotated n) (familyDualRotated n)
        (scheduleRotated n) (index n) (level n).normalY
        (level n).normalX := fun n => by
    convert (level n).rotatedVertical using 1
    · exact P.axisSwap_orbitBox n
    · exact Pdual.axisSwap_orbitBox n
    all_goals exact cast_heq _ _
  let rotatedHorizontalLevel : forall n,
      AlignedExactExtentPairedMixedBoundaryScores
        E.axisSwap Edual.axisSwap mu muDual
        (P.axisSwap.orbitBox n) (Pdual.axisSwap.orbitBox n)
        (score n) (scoreDual n) (familyRotated n) (familyDualRotated n)
        (scheduleRotated n) (index n) (level n).rotatedHorizontalX
        (level n).rotatedHorizontalY := fun n => by
    convert (level n).rotatedHorizontal using 1
    · exact P.axisSwap_orbitBox n
    · exact Pdual.axisSwap_orbitBox n
    all_goals exact cast_heq _ _
  have hnormalLimit := hnormal index
    (fun n => (level n).normalX) (fun n => (level n).normalY)
    (fun n => (level n).normal) normalSlack
  have hrotatedVerticalLimit := hrotatedDual index
    (fun n => (level n).normalY) (fun n => (level n).normalX)
    rotatedVerticalLevel rotatedSlack
  have hrotatedHorizontalLimit := hrotatedDual index
    (fun n => (level n).rotatedHorizontalX)
    (fun n => (level n).rotatedHorizontalY)
    rotatedHorizontalLevel rotatedSlack
  exact ⟨{
    score := score
    scoreDual := scoreDual
    family := family
    familyDual := familyDual
    schedule := schedule
    index := index
    level := level
    familyRotated := familyRotated
    familyDualRotated := familyDualRotated
    scheduleRotated := scheduleRotated
    rotatedVerticalLevel := rotatedVerticalLevel
    rotatedHorizontalLevel := rotatedHorizontalLevel
    rotatedVerticalLevel_heq := fun n => cast_heq _ _
    rotatedHorizontalLevel_heq := fun n => cast_heq _ _
    normalLimit := hnormalLimit
    dualRotatedVerticalLimit := hrotatedVerticalLimit
    dualRotatedHorizontalLimit := hrotatedHorizontalLimit }⟩

end StatMech.FK.PeriodicPlanar
