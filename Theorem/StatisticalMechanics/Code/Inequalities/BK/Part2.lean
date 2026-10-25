/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Inequalities.BK.Part2
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace


variable {E F : Type*}


lemma wprob_mono [Fintype E] [DecidableEq E] {φ : E → Bool → ℝ} (hφ : ∀ x b, 0 ≤ φ x b)
    {S T : Set (ConfigSpace E)} (h : S ⊆ T) : wprob φ S ≤ wprob φ T := by
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_right _ (pweight_nonneg hφ ω)
  by_cases hS : ω ∈ S
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem (h hS)]
  · rw [Set.indicator_of_notMem hS]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω


lemma wprob_union_inter [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (U V : Set (ConfigSpace E)) :
    wprob φ (U ∪ V) + wprob φ (U ∩ V) = wprob φ U + wprob φ V := by
  simp only [wprob, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hU : ω ∈ U <;> by_cases hV : ω ∈ V <;>
    simp [Set.indicator, hU, hV, Set.mem_union, Set.mem_inter_iff]


lemma bk_algebra (a0 a1 b0 b1 p q c0 c1 m : ℝ)
    (hq : q = 1 - p) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hmab : m ≤ a0 * b0) (hc0m : c0 ≤ m)
    (hc1u : c1 ≤ a0 * b1 + a1 * b0 - m) (hc1v : c1 ≤ a1 * b1) :
    q * c0 + p * c1 ≤ (q * a0 + p * a1) * (q * b0 + p * b1) := by
  have key1 : q * p * c1 ≤ q * p * (a0 * b1 + a1 * b0 - m) :=
    mul_le_mul_of_nonneg_left hc1u (mul_nonneg hq0 hp0)
  have key2 : p * p * c1 ≤ p * p * (a1 * b1) :=
    mul_le_mul_of_nonneg_left hc1v (mul_nonneg hp0 hp0)
  have key3 : q * c0 ≤ q * m := mul_le_mul_of_nonneg_left hc0m hq0
  have key4 : q * q * m ≤ q * q * (a0 * b0) :=
    mul_le_mul_of_nonneg_left hmab (mul_nonneg hq0 hq0)
  have hpsplit : p * c1 = q * p * c1 + p * p * c1 := by rw [hq]; ring
  have hqsq : q * m = q * q * m + q * p * m := by rw [hq]; ring
  calc q * c0 + p * c1
      ≤ q * m + (q * p * c1 + p * p * c1) := by rw [hpsplit]; linarith [key3]
    _ ≤ q * m + (q * p * (a0 * b1 + a1 * b0 - m) + p * p * (a1 * b1)) := by linarith [key1, key2]
    _ = (q * q * m + q * p * m) + (q * p * (a0 * b1 + a1 * b0 - m) + p * p * (a1 * b1)) := by
          rw [hqsq]
    _ ≤ (q * q * (a0 * b0) + q * p * m)
          + (q * p * (a0 * b1 + a1 * b0 - m) + p * p * (a1 * b1)) := by linarith [key4]
    _ = (q * a0 + p * a1) * (q * b0 + p * b1) := by ring


end StatMech
