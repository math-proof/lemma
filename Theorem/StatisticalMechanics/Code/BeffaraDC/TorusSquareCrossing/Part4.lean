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
import Def.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossing.Part4
open SimpleGraph Set
open scoped BigOperators


namespace StatMech.BeffaraDC

open StatMech.Onsager


@[simp] theorem mem_torusAmbientDualPullbackEvent (L : ℕ) [Fact (2 < L)]
    {A : Finset (TorusAmbientConfig L)} {omega : TorusAmbientConfig L} :
    omega ∈ torusAmbientDualPullbackEvent L A ↔
      torusCellDualAmbientConfig L omega ∈ A := by
  simp [torusAmbientDualPullbackEvent]


theorem torusAmbientProbability_le_q_mul_dual
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {q : ℝ} (hq1 : 1 ≤ q) :
    torusAmbientProbability L (selfDualPoint q) q omega ≤
      q * torusAmbientProbability L (selfDualPoint q) q
        (torusCellDualAmbientConfig L omega) := by
  have hq : 0 < q := lt_of_lt_of_le one_pos hq1
  obtain ⟨hp, hp1⟩ := selfDualPoint_mem_Ioo hq
  have hdualpos : 0 < torusAmbientProbability L (selfDualPoint q) q
      (torusCellDualAmbientConfig L omega) := by
    unfold torusAmbientProbability
    exact div_pos (torusAmbientFKWeight_pos L _ hp hp1 hq)
      (torusAmbientPartition_pos L hp hp1 hq)
  have hr := (torusAmbientProbability_selfDual_ratio_mem L omega hq1).2
  rwa [div_le_iff₀ hdualpos] at hr


theorem torusAmbientDualPullbackEventProbability_le
    (L : ℕ) [Fact (2 < L)] (A : Finset (TorusAmbientConfig L))
    {q : ℝ} (hq1 : 1 ≤ q) :
    torusAmbientEventProbability L (selfDualPoint q) q
        (torusAmbientDualPullbackEvent L A) ≤
      q * torusAmbientEventProbability L (selfDualPoint q) q A := by
  unfold torusAmbientEventProbability
  calc
    (∑ omega : TorusAmbientConfig L,
        if omega ∈ torusAmbientDualPullbackEvent L A then
          torusAmbientProbability L (selfDualPoint q) q omega else 0) ≤
      ∑ omega : TorusAmbientConfig L,
        if torusCellDualAmbientConfig L omega ∈ A then
          q * torusAmbientProbability L (selfDualPoint q) q
            (torusCellDualAmbientConfig L omega) else 0 := by
        apply Finset.sum_le_sum
        intro omega _
        simp only [mem_torusAmbientDualPullbackEvent]
        split <;> simp_all [torusAmbientProbability_le_q_mul_dual L omega hq1]
    _ = q * ∑ eta : TorusAmbientConfig L,
        if eta ∈ A then torusAmbientProbability L (selfDualPoint q) q eta else 0 := by
      have hsum := Equiv.sum_comp (torusCellDualAmbientConfigEquiv L)
        (fun eta : TorusAmbientConfig L =>
          if eta ∈ A then torusAmbientProbability L (selfDualPoint q) q eta else 0)
      have hsum' : (∑ omega : TorusAmbientConfig L,
          if torusCellDualAmbientConfig L omega ∈ A then
            torusAmbientProbability L (selfDualPoint q) q
              (torusCellDualAmbientConfig L omega) else 0) =
          ∑ eta : TorusAmbientConfig L,
            if eta ∈ A then
              torusAmbientProbability L (selfDualPoint q) q eta else 0 := by
        simpa only [torusCellDualAmbientConfigEquiv] using hsum
      calc
        (∑ omega : TorusAmbientConfig L,
            if torusCellDualAmbientConfig L omega ∈ A then
              q * torusAmbientProbability L (selfDualPoint q) q
                (torusCellDualAmbientConfig L omega) else 0) =
          q * ∑ omega : TorusAmbientConfig L,
            if torusCellDualAmbientConfig L omega ∈ A then
              torusAmbientProbability L (selfDualPoint q) q
                (torusCellDualAmbientConfig L omega) else 0 := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro omega _
                  split <;> simp_all
        _ = q * ∑ eta : TorusAmbientConfig L,
            if eta ∈ A then
              torusAmbientProbability L (selfDualPoint q) q eta else 0 := by
                exact congrArg (fun x : ℝ => q * x) hsum'


end StatMech.BeffaraDC
