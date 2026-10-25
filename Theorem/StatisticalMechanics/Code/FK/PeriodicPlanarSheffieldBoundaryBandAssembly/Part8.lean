/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandPadding.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part5
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


theorem PeriodicPlanarDualPair.TwoLevelRectangleArray.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B : Real} (data : D.TwoLevelRectangleArray mu B) : False := by
  let a : Nat → Nat → Real := fun n k => if k = 0 then data.a0 n else data.a1 n
  let b : Nat → Nat → Real := fun n k => if k = 0 then data.b0 n else data.b1 n
  let c : Nat → Nat → Real := fun n k => if k = 0 then data.c0 n else data.c1 n
  let d : Nat → Nat → Real := fun n k => if k = 0 then data.d0 n else data.d1 n
  let K : Nat → Nat := fun _ => 0
  apply D.adjacent_rectangles_contradiction_of_max_limits mu
    (B := B) data.Bpos data.primalArcBound data.dualArcBound a b c d K
  · intro n k
    by_cases hk : k = 0
    · simpa [a, b, hk] using data.spanX0 n
    · simpa [a, b, hk] using data.spanX1 n
  · intro n k
    by_cases hk : k = 0
    · simpa [c, d, hk] using data.spanY0 n
    · simpa [c, d, hk] using data.spanY1 n
  · simpa [a, b, c, d] using data.verticalStart
  · simpa [a, b, c, d, K] using data.horizontalEnd
  · intro k hk
    have hk0 : ∀ n, k n = 0 := by
      intro n
      have := hk n
      dsimp only [K] at this
      omega
    simpa only [a, b, c, d, hk0, if_pos, Nat.zero_add] using
      data.primalAdjacent
  · intro k
    let q0 : Nat → Real := fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (data.a0 n + 4 * B) (data.b0 n - 4 * B)
          (data.c0 n) (data.d0 n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (data.a0 n) (data.b0 n) (data.c0 n + 4 * B)
          (data.d0 n - 4 * B)))
    let q1 : Nat → Real := fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (data.a1 n + 4 * B) (data.b1 n - 4 * B)
          (data.c1 n) (data.d1 n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (data.a1 n) (data.b1 n) (data.c1 n + 4 * B)
          (data.d1 n - 4 * B)))
    let q : Nat → Real := fun n => if k n = 0 then q0 n else q1 n
    have hq0 : Tendsto q0 atTop (nhds 1) := by
      simpa only [q0] using data.dualLevel0
    have hq1 : Tendsto q1 atTop (nhds 1) := by
      simpa only [q1] using data.dualLevel1
    have hlower : ∀ n, min (q0 n) (q1 n) ≤ q n := by
      intro n
      by_cases hn : k n = 0
      · simp [q, hn]
      · simp [q, hn]
    have hupper : ∀ n, q n ≤ 1 := by
      intro n
      by_cases hn : k n = 0
      · simp only [q, hn, if_pos, q0]
        exact max_le measureReal_le_one measureReal_le_one
      · simp only [q, hn, if_neg, q1]
        exact max_le measureReal_le_one measureReal_le_one
    have hq' := (hq0.min hq1).squeeze tendsto_const_nhds hlower
      (fun n => by simpa using hupper n)
    have hq : Tendsto q atTop (nhds 1) := by simpa using hq'
    apply hq.congr'
    filter_upwards with n
    by_cases hn : k n = 0 <;>
      simp [q, q0, q1, a, b, c, d, hn]

end StatMech.FK.PeriodicPlanar
