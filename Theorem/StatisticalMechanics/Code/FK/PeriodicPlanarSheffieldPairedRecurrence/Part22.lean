/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part14
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem exists_pairedAdjacentOutwardScheduleData
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
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    Nonempty (PairedAdjacentOutwardScheduleData
      E Edual mu muDual step pad) := by
  let base := Classical.choice
    (exists_pairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual hFKG hTI hunique hFKGDual hTIDual huniqueDual
        step hstep)
  obtain ⟨outwardRadiusDual, houtward⟩ :=
    Edual.exists_uniformOutwardBoundaryCrossingRadius
      muDual hFKGDual hTIDual huniqueDual pad hpad
  let requirement : Nat -> Nat := fun m => max
    (E.connectorMarginRequirement (base.radius m))
    (Edual.connectorMarginRequirement (outwardRadiusDual m))
  let schedule : forall m, PairedAlignedMarginSchedule E Edual
      (base.family m) (base.familyDual m)
      (fun _ => requirement m) (fun _ => requirement m) := fun m =>
    Classical.choice (exists_pairedAlignedMarginSchedule E Edual
      (base.family m) (base.familyDual m)
      (fun _ => requirement m) (fun _ => requirement m))
  exact ⟨{
    base := base
    outwardRadiusDual := outwardRadiusDual
    outwardContinuationDual := houtward
    schedule := schedule }⟩


theorem PeriodicPlanarDualPair.exists_canonicalPairedAdjacentOutwardScheduleData_of_common
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcommon :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1)
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    Nonempty (PairedAdjacentOutwardScheduleData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) step pad) := by
  dsimp only
  letI : IsProbabilityMeasure
      (D.dualMeasure
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V)))) :=
    inferInstance
  have hdata := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  exact exists_pairedAdjacentOutwardScheduleData
    D.primalEmbedding D.dualEmbedding _ _
      hdata.1 hdata.2.1 hdata.2.2.2.2.1
      hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.2
      step hstep pad hpad


end StatMech.FK.PeriodicPlanar
