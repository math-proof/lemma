/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part13
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem exists_pairedAdjacentBoundaryBandScheduleData
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
    (step : Nat -> Int) (hstep : forall n, 0 <= step n) :
    Nonempty (PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- hunique]
    exact measure_mono fun _ h => h.1
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  obtain ⟨radius, hmerge, hprimal⟩ :=
    E.exists_uniformTemplateAdjacentBoundaryBandCrossingRadius_with_pairMerge
      mu hFKG hTI hunique (fun n => P.orbitBox n) hhit step hstep
  obtain ⟨radiusDual, hdual⟩ :=
    Edual.exists_uniformRadius_boundaryBandScores_crossing_max_tendsto_one
      muDual hFKGDual hTIDual huniqueDual
  obtain ⟨score, scoreDual, family, familyDual,
      hscore, hscore_le, hscoreDual, hscoreDual_le⟩ :=
    exists_pairedCofinalNormalBoundaryBandFamilies_bounded
      E Edual mu muDual hFKG hTI hunique
        hFKGDual hTIDual huniqueDual
  let requirement : Nat -> Nat := fun m => max
    (E.connectorMarginRequirement (radius m))
    (Edual.connectorMarginRequirement (radiusDual m))
  let schedule : forall m, PairedAlignedMarginSchedule E Edual
      (family m) (familyDual m) (fun _ => requirement m)
        (fun _ => requirement m) := fun m =>
    Classical.choice (exists_pairedAlignedMarginSchedule E Edual
      (family m) (familyDual m) (fun _ => requirement m)
        (fun _ => requirement m))
  refine ⟨{
    step_nonneg := hstep
    radius := radius
    radiusDual := radiusDual
    score := score
    scoreDual := scoreDual
    family := family
    familyDual := familyDual
    primalContinuation := ?_
    primalMerge := hmerge
    dualContinuation := ?_
    score_tendsto := hscore
    score_le_one := hscore_le
    scoreDual_tendsto := hscoreDual
    scoreDual_le_one := hscoreDual_le
    schedule := schedule }⟩
  · simpa [PeriodicPlaneEmbedding.UniformAdjacentBoundaryBandCrossingRadius]
      using hprimal
  · exact hdual


theorem PeriodicPlanarDualPair.exists_canonicalPairedAdjacentBoundaryBandScheduleData_of_common
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcommon :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1)
    (step : Nat -> Int) (hstep : forall n, 0 <= step n) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    Nonempty (PairedAdjacentBoundaryBandScheduleData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) step) := by
  dsimp only
  letI : IsProbabilityMeasure
      (D.dualMeasure
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V)))) :=
    inferInstance
  have hdata := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  exact exists_pairedAdjacentBoundaryBandScheduleData
    D.primalEmbedding D.dualEmbedding _ _
      hdata.1 hdata.2.1 hdata.2.2.2.2.1
      hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.2 step hstep


end StatMech.FK.PeriodicPlanar
