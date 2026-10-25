/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellRN.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Def.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossing.Part6
open SimpleGraph Set
open scoped BigOperators


namespace StatMech.BeffaraDC

open StatMech.Onsager


@[simp] theorem mem_torusSquareVerticalCrossingEvent
    (L : ℕ) [Fact (2 < L)] (n : ℕ) (omega : TorusAmbientConfig L) :
    omega ∈ torusSquareVerticalCrossingEvent L n ↔
      torusSquareHorizontalCrossing L n (torusAmbientSwapConfig L omega) := by
  simp [torusSquareVerticalCrossingEvent]


theorem torus_squareCrossing_ge_one_div_one_add_q
    (L : ℕ) [Fact (2 < L)] (horizontal : Finset (TorusAmbientConfig L))
    {q : ℝ} (hq1 : 1 ≤ q)
    (hdualCrossing : ∀ omega : TorusAmbientConfig L,
      omega ∉ horizontal ↔
        torusCellDualAmbientConfig L omega ∈
          torusAmbientRotatedEvent L horizontal) :
    1 / (1 + q) ≤
      torusAmbientEventProbability L (selfDualPoint q) q horizontal := by
  let vertical := torusAmbientRotatedEvent L horizontal
  let dualVertical := torusAmbientDualPullbackEvent L vertical
  have hsum : torusAmbientEventProbability L (selfDualPoint q) q horizontal +
      torusAmbientEventProbability L (selfDualPoint q) q dualVertical = 1 := by
    unfold torusAmbientEventProbability
    rw [← Finset.sum_add_distrib]
    calc
      (∑ omega : TorusAmbientConfig L,
          ((if omega ∈ horizontal then
              torusAmbientProbability L (selfDualPoint q) q omega else 0) +
            if omega ∈ dualVertical then
              torusAmbientProbability L (selfDualPoint q) q omega else 0)) =
        ∑ omega : TorusAmbientConfig L,
          torusAmbientProbability L (selfDualPoint q) q omega := by
            apply Finset.sum_congr rfl
            intro omega _
            have hmem : omega ∈ dualVertical ↔ omega ∉ horizontal := by
              simpa [dualVertical, vertical] using (hdualCrossing omega).symm
            by_cases hh : omega ∈ horizontal <;> simp [hh, hmem]
      _ = 1 := by
        have hq : 0 < q := lt_of_lt_of_le one_pos hq1
        obtain ⟨hp, hp1⟩ := selfDualPoint_mem_Ioo hq
        exact torusAmbientProbability_sum_one L hp hp1 hq
  have hdualLe : torusAmbientEventProbability L (selfDualPoint q) q dualVertical ≤
      q * torusAmbientEventProbability L (selfDualPoint q) q horizontal := by
    calc
      torusAmbientEventProbability L (selfDualPoint q) q dualVertical ≤
          q * torusAmbientEventProbability L (selfDualPoint q) q vertical :=
        torusAmbientDualPullbackEventProbability_le L vertical hq1
      _ = q * torusAmbientEventProbability L (selfDualPoint q) q horizontal := by
        rw [torusAmbientEventProbability_rotated]
  exact dlt_square_crossing_estimate (by positivity) hsum hdualLe


theorem torus_concreteSquareCrossing_ge_one_div_one_add_q
    (L : ℕ) [Fact (2 < L)] (n : ℕ) (_hn : 1 ≤ n) (_hnL : n < L)
    {q : ℝ} (hq1 : 1 ≤ q)
    (hdualCrossing : ∀ omega : TorusAmbientConfig L,
      ¬ torusSquareHorizontalCrossing L n omega ↔
        torusCellDualAmbientConfig L omega ∈
          torusSquareVerticalCrossingEvent L n) :
    1 / (1 + q) ≤
      torusAmbientEventProbability L (selfDualPoint q) q
        (torusSquareHorizontalCrossingEvent L n) := by
  apply torus_squareCrossing_ge_one_div_one_add_q L
    (torusSquareHorizontalCrossingEvent L n) hq1
  intro omega
  simpa [torusSquareVerticalCrossingEvent] using hdualCrossing omega


theorem torus_squareCrossing_const_pos {q : ℝ} (hq1 : 1 ≤ q) :
    0 < 1 / (1 + q) := by
  positivity

end StatMech.BeffaraDC
