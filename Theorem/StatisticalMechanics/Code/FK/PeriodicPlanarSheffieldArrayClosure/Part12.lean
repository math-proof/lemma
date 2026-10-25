/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part6
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


theorem PeriodicPlanarDualPair.TwoLevelBoundaryScoreArray.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {B : Real}
    (data : D.TwoLevelBoundaryScoreArray mu B) : False := by
  have hvertical :=
    D.primalEmbedding.verticalCrossing_tendsto_one_of_boundaryScores
      mu hFKG
      (fun n ↦ data.a0 n + 4 * B) (fun n ↦ data.b0 n - 4 * B)
      data.c0 data.d0 data.bottomSource data.topSource
      data.bottomLimit data.topLimit data.verticalMergeLimit
  have hhorizontal :=
    D.primalEmbedding.horizontalCrossing_tendsto_one_of_boundaryScores
      mu hFKG data.a1 data.b1
      (fun n ↦ data.c1 n + 4 * B) (fun n ↦ data.d1 n - 4 * B)
      data.leftSource data.rightSource
      data.leftLimit data.rightLimit data.horizontalMergeLimit
  exact PeriodicPlanarDualPair.TwoLevelRectangleArray.false D mu {
    Bpos := data.Bpos
    primalArcBound := data.primalArcBound
    dualArcBound := data.dualArcBound
    a0 := data.a0
    b0 := data.b0
    c0 := data.c0
    d0 := data.d0
    a1 := data.a1
    b1 := data.b1
    c1 := data.c1
    d1 := data.d1
    spanX0 := data.spanX0
    spanY0 := data.spanY0
    spanX1 := data.spanX1
    spanY1 := data.spanY1
    verticalStart := hvertical
    horizontalEnd := hhorizontal
    primalAdjacent := data.primalAdjacent
    dualLevel0 := data.dualLevel0
    dualLevel1 := data.dualLevel1 }


theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_boundaryScoreArray
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (harray :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 →
        ∃ B : Real, Nonempty (D.TwoLevelBoundaryScoreArray mu B)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only
  intro hcommon
  have hdata := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  obtain ⟨B, ⟨data⟩⟩ := harray hcommon
  exact data.false D _ hdata.1

end StatMech.FK.PeriodicPlanar
