/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldVariablePadding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRotatedBoundaryBands.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlanarDualPair.VariablePadTwoLevelRectangleArray.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B : Real} (data : D.VariablePadTwoLevelRectangleArray mu B) : False := by
  let horizontal : Nat → Nat → Real := fun n k ↦ if k = 0 then
    mu.real (D.primalEmbedding.horizontalCrossingEvent
      (data.a0 n) (data.b0 n)
      (data.c0 n + data.yPad0 n) (data.d0 n - data.yPad0 n))
  else mu.real (D.primalEmbedding.horizontalCrossingEvent
      (data.a1 n) (data.b1 n)
      (data.c1 n + data.yPad1 n) (data.d1 n - data.yPad1 n))
  let vertical : Nat → Nat → Real := fun n k ↦ if k = 0 then
    mu.real (D.primalEmbedding.verticalCrossingEvent
      (data.a0 n + data.xPad0 n) (data.b0 n - data.xPad0 n)
      (data.c0 n) (data.d0 n))
  else mu.real (D.primalEmbedding.verticalCrossingEvent
      (data.a1 n + data.xPad1 n) (data.b1 n - data.xPad1 n)
      (data.c1 n) (data.d1 n))
  let dualVertical : Nat → Nat → Real := fun n k ↦ if k = 0 then
    mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.a0 n + data.xPad0 n) (data.b0 n - data.xPad0 n)
        (data.c0 n) (data.d0 n))
  else mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.a1 n + data.xPad1 n) (data.b1 n - data.xPad1 n)
        (data.c1 n) (data.d1 n))
  let dualHorizontal : Nat → Nat → Real := fun n k ↦ if k = 0 then
    mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.a0 n) (data.b0 n)
        (data.c0 n + data.yPad0 n) (data.d0 n - data.yPad0 n))
  else mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.a1 n) (data.b1 n)
        (data.c1 n + data.yPad1 n) (data.d1 n - data.yPad1 n))
  let K : Nat → Nat := fun _ ↦ 0
  apply adjacent_height_array_contradiction_of_primal_dual_bounded_limits
    horizontal vertical dualVertical dualHorizontal K
  · intro n k
    by_cases hk : k = 0 <;> simp [horizontal, hk, measureReal_nonneg]
  · intro n k
    by_cases hk : k = 0 <;> simp [vertical, hk, measureReal_nonneg]
  · intro n k
    by_cases hk : k = 0 <;> simp [horizontal, hk, measureReal_le_one]
  · intro n k
    by_cases hk : k = 0 <;> simp [vertical, hk, measureReal_le_one]
  · simpa [vertical] using data.verticalStart
  · simpa [horizontal, K] using data.horizontalEnd
  · intro n k
    by_cases hk : k = 0
    · simpa [horizontal, dualVertical, hk] using
        D.matchedCrossing_measureReal_add_le_one_of_pads mu
          data.Bpos data.primalArcBound data.dualArcBound
          (data.xPad0_ge n) (data.yPad0_ge n)
          (data.spanX0 n) (data.spanY0 n)
    · simpa [horizontal, dualVertical, hk] using
        D.matchedCrossing_measureReal_add_le_one_of_pads mu
          data.Bpos data.primalArcBound data.dualArcBound
          (data.xPad1_ge n) (data.yPad1_ge n)
          (data.spanX1 n) (data.spanY1 n)
  · intro n k
    by_cases hk : k = 0
    · simpa [vertical, dualHorizontal, hk] using
        D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads mu
          data.Bpos data.primalArcBound data.dualArcBound
          (data.xPad0_ge n) (data.yPad0_ge n)
          (data.spanX0 n) (data.spanY0 n)
    · simpa [vertical, dualHorizontal, hk] using
        D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads mu
          data.Bpos data.primalArcBound data.dualArcBound
          (data.xPad1_ge n) (data.yPad1_ge n)
          (data.spanX1 n) (data.spanY1 n)
  · intro k hk
    have hk0 : ∀ n, k n = 0 := by
      intro n
      have h := hk n
      dsimp only [K] at h
      omega
    simpa [horizontal, vertical, hk0] using data.primalAdjacent
  · intro k _hk
    let q0 : Nat → Real := fun n ↦ max (dualVertical n 0)
      (dualHorizontal n 0)
    let q1 : Nat → Real := fun n ↦ max (dualVertical n 1)
      (dualHorizontal n 1)
    let q : Nat → Real := fun n ↦ if k n = 0 then q0 n else q1 n
    have hq0 : Tendsto q0 atTop (nhds 1) := by
      simpa [q0, dualVertical, dualHorizontal] using data.dualLevel0
    have hq1 : Tendsto q1 atTop (nhds 1) := by
      simpa [q1, dualVertical, dualHorizontal] using data.dualLevel1
    have hlower : ∀ n, min (q0 n) (q1 n) ≤ q n := by
      intro n
      by_cases hn : k n = 0 <;> simp [q, hn]
    have hupper : ∀ n, q n ≤ 1 := by
      intro n
      by_cases hn : k n = 0 <;>
        simp [q, q0, q1, dualVertical, dualHorizontal, hn,
          measureReal_le_one]
    have hq' := (hq0.min hq1).squeeze tendsto_const_nhds hlower
      (fun n ↦ by simpa using hupper n)
    have hq : Tendsto q atTop (nhds 1) := by simpa using hq'
    apply hq.congr'
    filter_upwards with n
    by_cases hn : k n = 0
    · simp [q, q0, hn]
    · have hk1 : k n = 1 := by
        have h := _hk n
        dsimp only [K] at h
        omega
      simp [q, q1, hn, hk1]

end StatMech.FK.PeriodicPlanar
