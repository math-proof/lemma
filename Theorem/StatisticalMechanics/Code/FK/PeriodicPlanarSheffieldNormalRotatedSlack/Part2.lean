/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalRotatedSlack.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldNormalRotatedSlack
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem NormalRotatedInsetLimitData.normalWideInset_eq_rotatedY
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding)
    (n : Nat) :
    (data.level n).normal.raw.wideLeftInt + padding +
        (data.level n).rotatedY =
      (data.level n).normal.raw.wideRightInt - padding := by
  have hspan := (data.level n).normalSpan_eq
  omega


theorem NormalRotatedInsetLimitData.normalWideInset_real_eq_rotatedY
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding)
    (n : Nat) :
    (data.level n).normal.raw.data.wideLeft + padding +
        (data.level n).rotatedY =
      (data.level n).normal.raw.data.wideRight - padding := by
  rw [(data.level n).normal.raw.wideLeft_eq,
    (data.level n).normal.raw.wideRight_eq]
  exact_mod_cast data.normalWideInset_eq_rotatedY n


theorem NormalRotatedInsetLimitData.rotatedWideRight_eq_left_add_normalY
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding)
    (n : Nat) :
    (data.level n).rotated.raw.wideRightInt =
      (data.level n).rotated.raw.wideLeftInt +
        (data.level n).normalY := by
  have hspan := (data.level n).rotatedSpan_eq
  omega


theorem NormalRotatedInsetLimitData.rotatedWide_real_eq_normalY
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding)
    (n : Nat) :
    (data.level n).rotated.raw.data.wideRight =
      (data.level n).rotated.raw.data.wideLeft +
        (data.level n).normalY := by
  rw [(data.level n).rotated.raw.wideLeft_eq,
    (data.level n).rotated.raw.wideRight_eq]
  exact_mod_cast data.rotatedWideRight_eq_left_add_normalY n


theorem NormalRotatedInsetLimitData.rotatedX_le_normalY
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding)
    (n : Nat) : (data.level n).rotatedX <= (data.level n).normalY := by
  have hspan := (data.level n).rotated.raw.extentX_le_wideSpan
  have heq := data.rotatedWideRight_eq_left_add_normalY n
  rw [heq] at hspan
  norm_num at hspan
  exact_mod_cast hspan


theorem NormalRotatedInsetLimitData.rotatedOriginalLimit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))} {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding) :
    Tendsto (fun n => max
      (mu.real (E.verticalCrossingEvent
        0 (data.level n).rotatedY 0 (data.level n).rotatedX))
      (mu.real (E.horizontalCrossingEvent
        0 (data.level n).rotatedY
        (data.rotatedLevel n).raw.data.wideLeft
        (data.rotatedLevel n).raw.data.wideRight)))
      atTop (nhds 1) := by
  exact E.axisSwap_crossingMax_tendsto_one mu
    (fun _ => 0) (fun n => (data.level n).rotatedX)
    (fun _ => 0) (fun n => (data.level n).rotatedY)
    (fun n => (data.rotatedLevel n).raw.data.wideLeft)
    (fun n => (data.rotatedLevel n).raw.data.wideRight)
    (fun _ => 0) (fun n => (data.level n).rotatedY)
    data.rotatedLimit


theorem NormalRotatedInsetLimitData.dualRotatedOriginalLimit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding) :
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        0 (data.level n).rotatedY 0 (data.level n).rotatedX))
      (muDual.real (Edual.horizontalCrossingEvent
        0 (data.level n).rotatedY
        (data.rotatedLevel n).raw.data.wideLeft
        (data.rotatedLevel n).raw.data.wideRight)))
      atTop (nhds 1) := by
  exact Edual.axisSwap_crossingMax_tendsto_one muDual
    (fun _ => 0) (fun n => (data.level n).rotatedX)
    (fun _ => 0) (fun n => (data.level n).rotatedY)
    (fun n => (data.rotatedLevel n).raw.data.wideLeft)
    (fun n => (data.rotatedLevel n).raw.data.wideRight)
    (fun _ => 0) (fun n => (data.level n).rotatedY)
    data.dualRotatedLimit


theorem NormalRotatedInsetLimitData.exists_primalDualFixedBranchesSubsequence
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {padding : Nat}
    (data : NormalRotatedInsetLimitData E Edual mu muDual padding) :
    let H0 : Nat -> Real := fun n => mu.real
      (E.horizontalCrossingEvent
        0 (data.level n).normalX 0 (data.level n).normalY)
    let V1 : Nat -> Real := fun n => mu.real
      (E.verticalCrossingEvent
        (data.level n).normal.raw.data.wideLeft
        (data.level n).normal.raw.data.wideRight
        0 (data.level n).normalY)
    let V0 : Nat -> Real := fun n => muDual.real
      (Edual.verticalCrossingEvent
        0 (data.level n).rotatedY 0 (data.level n).rotatedX)
    let H1 : Nat -> Real := fun n => muDual.real
      (Edual.horizontalCrossingEvent
        0 (data.level n).rotatedY
        (data.rotatedLevel n).raw.data.wideLeft
        (data.rotatedLevel n).raw.data.wideRight)
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
  dsimp only
  exact tendsto_two_max_one_fixedBranches_subsequence _ _ _ _
    data.normalLimit data.dualRotatedOriginalLimit


theorem nonempty_normalRotatedInsetLimitData_of_unique
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (padding : Nat) :
    Nonempty (NormalRotatedInsetLimitData
      E Edual mu muDual padding) := by
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
    all_goals
      exact cast_heq _ _
  obtain ⟨radius, hnormal⟩ :=
    E.exists_uniformOrbitBoxMixedRadius_alignedExact_primalLimit
      Edual mu muDual hFKG hTI hunique score scoreDual family familyDual
      schedule hscore hscore_le
  obtain ⟨radiusRotated, hrotated⟩ :=
    E.axisSwap.exists_uniformOrbitBoxMixedRadius_alignedExact_primalLimit
      Edual.axisSwap mu muDual hFKG
      (P.axisSwap_isTranslationInvariant mu hTI) hunique score scoreDual
      familyRotated familyDualRotated scheduleRotated hscore hscore_le
  obtain ⟨radiusDual, hnormalDual⟩ :=
    E.exists_uniformOrbitBoxMixedRadius_alignedExact_dualLimit
      Edual mu muDual hFKGDual hTIDual huniqueDual score scoreDual
      family familyDual schedule hscoreDual hscoreDual_le
  obtain ⟨radiusDualRotated, hrotatedDual⟩ :=
    E.axisSwap.exists_uniformOrbitBoxMixedRadius_alignedExact_dualLimit
      Edual.axisSwap mu muDual hFKGDual
      (Pdual.axisSwap_isTranslationInvariant muDual hTIDual) huniqueDual
      score scoreDual familyRotated familyDualRotated scheduleRotated
      hscoreDual hscoreDual_le
  let radiusNormalShared : Nat -> Nat := fun n =>
    max (max (radius n) n) (max (radiusDual n) n)
  let radiusRotatedShared : Nat -> Nat := fun n =>
    max (max (radiusRotated n) n) (max (radiusDualRotated n) n)
  have hslack (n : Nat) :=
    exists_pairedAlignedNormalRotatedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n)
      (radiusNormalShared n) (radiusRotatedShared n)
  let index : Nat -> Nat := fun n => Classical.choose (hslack n)
  let normalSlack : forall n, PairedAlignedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n)
      (max (radius n) n) (index n) := fun n =>
    PairedAlignedConnectorSlack.of_le E Edual
      (Nat.le_max_left _ _) (Classical.choose_spec (hslack n)).1
  let normalSlackDual : forall n, PairedAlignedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n)
      (max (radiusDual n) n) (index n) := fun n =>
    PairedAlignedConnectorSlack.of_le E Edual
      (Nat.le_max_right _ _) (Classical.choose_spec (hslack n)).1
  let rotatedSlackShared : forall n,
      PairedAlignedConnectorSlack E.axisSwap Edual.axisSwap
        (familyRotated n) (familyDualRotated n) (scheduleRotated n)
        (radiusRotatedShared n) (index n) := fun n =>
    by
      convert (Classical.choose_spec (hslack n)).2 using 1
      · exact P.axisSwap_orbitBox n
      · exact Pdual.axisSwap_orbitBox n
      all_goals exact cast_heq _ _
  let rotatedSlack : forall n,
      PairedAlignedConnectorSlack E.axisSwap Edual.axisSwap
        (familyRotated n) (familyDualRotated n) (scheduleRotated n)
        (max (radiusRotated n) n) (index n) := fun n =>
    PairedAlignedConnectorSlack.of_le E.axisSwap Edual.axisSwap
      (Nat.le_max_left _ _) (rotatedSlackShared n)
  let rotatedSlackDual : forall n,
      PairedAlignedConnectorSlack E.axisSwap Edual.axisSwap
        (familyRotated n) (familyDualRotated n) (scheduleRotated n)
        (max (radiusDualRotated n) n) (index n) := fun n =>
    PairedAlignedConnectorSlack.of_le E.axisSwap Edual.axisSwap
      (Nat.le_max_right _ _) (rotatedSlackShared n)
  let level : forall n,
      AlignedNormalRotatedInsetPairedMixedBoundaryScores E Edual mu muDual
        (P.orbitBox n) (Pdual.orbitBox n) (score n) (scoreDual n)
        (family n) (familyDual n) (schedule n) (index n) padding := fun n =>
    Classical.choice
      (nonempty_alignedNormalRotatedInsetPairedMixedBoundaryScores
        E Edual mu muDual hTI hTIDual (family n) (familyDual n)
        (schedule n) (index n) padding)
  have hnormalLimit := hnormal index
    (fun n => (level n).normalX) (fun n => (level n).normalY)
    (fun n => (level n).normal) normalSlack
  let rotatedLevel : forall n,
      AlignedExactExtentPairedMixedBoundaryScores
        E.axisSwap Edual.axisSwap mu muDual
        (P.axisSwap.orbitBox n) (Pdual.axisSwap.orbitBox n)
        (score n) (scoreDual n) (familyRotated n) (familyDualRotated n)
        (scheduleRotated n) (index n) (level n).rotatedX
        (level n).rotatedY := fun n => by
    convert (level n).rotated using 1
    · exact P.axisSwap_orbitBox n
    · exact Pdual.axisSwap_orbitBox n
    all_goals exact cast_heq _ _
  have hrotatedLimit := hrotated index
    (fun n => (level n).rotatedX) (fun n => (level n).rotatedY)
    rotatedLevel rotatedSlack
  have hnormalDualLimit := hnormalDual index
    (fun n => (level n).normalX) (fun n => (level n).normalY)
    (fun n => (level n).normal) normalSlackDual
  have hrotatedDualLimit := hrotatedDual index
    (fun n => (level n).rotatedX) (fun n => (level n).rotatedY)
    rotatedLevel rotatedSlackDual
  have hrotatedLevelHeq (n : Nat) :
      rotatedLevel n ≍ (level n).rotated := by
    exact cast_heq _ _
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
    rotatedLevel := rotatedLevel
    rotatedLevel_heq := hrotatedLevelHeq
    normalLimit := hnormalLimit
    rotatedLimit := hrotatedLimit
    dualNormalLimit := hnormalDualLimit
    dualRotatedLimit := hrotatedDualLimit }⟩


end StatMech.FK.PeriodicPlanar
