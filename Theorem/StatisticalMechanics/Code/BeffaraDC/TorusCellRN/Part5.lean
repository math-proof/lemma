/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellFKDuality
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDefectClassify.Part3
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellRN.Part5
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


theorem torusAmbientProbability_sum_one (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ omega : TorusAmbientConfig L, torusAmbientProbability L p q omega = 1 := by
  have hZ : torusAmbientPartition L p q ≠ 0 :=
    ne_of_gt (torusAmbientPartition_pos L hp hp1 hq)
  have hZ' : (∑ omega : TorusAmbientConfig L,
      torusAmbientFKWeight L p q omega) ≠ 0 := by
    simpa [torusAmbientPartition] using hZ
  unfold torusAmbientProbability torusAmbientPartition
  rw [← Finset.sum_div, div_self hZ']


theorem torusAmbientProbability_ratio_eq_weight_ratio
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    torusAmbientProbability L p q omega /
        torusAmbientProbability L p q (torusCellDualAmbientConfig L omega) =
      torusAmbientFKWeight L p q omega /
        torusAmbientFKWeight L p q (torusCellDualAmbientConfig L omega) := by
  have hZ : torusAmbientPartition L p q ≠ 0 :=
    ne_of_gt (torusAmbientPartition_pos L hp hp1 hq)
  have hWD : torusAmbientFKWeight L p q
      (torusCellDualAmbientConfig L omega) ≠ 0 :=
    ne_of_gt (torusAmbientFKWeight_pos L _ hp hp1 hq)
  unfold torusAmbientProbability
  field_simp


theorem torusAmbientProbability_selfDual_ratio_eq_zpow
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {q : ℝ} (hq : 0 < q) :
    torusAmbientProbability L (selfDualPoint q) q omega /
        torusAmbientProbability L (selfDualPoint q) q
          (torusCellDualAmbientConfig L omega) =
      q ^ (torusAmbientDefect L omega - 1) := by
  obtain ⟨hp, hp1⟩ := selfDualPoint_mem_Ioo hq
  rw [torusAmbientProbability_ratio_eq_weight_ratio L omega hp hp1 hq]
  have hrel := torusAmbientFKWeight_selfDual_relation L omega hq
  have hqne : q ≠ 0 := ne_of_gt hq
  have hWD : torusAmbientFKWeight L (selfDualPoint q) q
      (torusCellDualAmbientConfig L omega) ≠ 0 :=
    ne_of_gt (torusAmbientFKWeight_pos L _ hp hp1 hq)
  rw [div_eq_iff hWD]
  apply mul_right_cancel₀ hqne
  calc
    torusAmbientFKWeight L (selfDualPoint q) q omega * q =
        torusAmbientFKWeight L (selfDualPoint q) q
          (torusCellDualAmbientConfig L omega) *
            q ^ torusAmbientDefect L omega := hrel
    _ = (q ^ (torusAmbientDefect L omega - 1) *
          torusAmbientFKWeight L (selfDualPoint q) q
            (torusCellDualAmbientConfig L omega)) * q := by
      have hpow : q ^ (torusAmbientDefect L omega - 1) * q =
          q ^ torusAmbientDefect L omega := by
        calc
          q ^ (torusAmbientDefect L omega - 1) * q =
              q ^ (torusAmbientDefect L omega - 1) * q ^ (1 : ℤ) := by
                rw [zpow_one]
          _ = q ^ ((torusAmbientDefect L omega - 1) + 1) := by
                rw [zpow_add₀ hqne]
          _ = q ^ torusAmbientDefect L omega := by ring_nf
      rw [← hpow]
      ring


theorem torusAmbientProbability_selfDual_ratio_values
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {q : ℝ} (hq : 0 < q) :
    let ratio := torusAmbientProbability L (selfDualPoint q) q omega /
      torusAmbientProbability L (selfDualPoint q) q
        (torusCellDualAmbientConfig L omega)
    ratio = q⁻¹ ∨ ratio = 1 ∨ ratio = q := by
  obtain ⟨hp, hp1⟩ := selfDualPoint_mem_Ioo hq
  rw [torusAmbientProbability_ratio_eq_weight_ratio L omega hp hp1 hq]
  have hrel := torusAmbientFKWeight_selfDual_relation L omega hq
  have hqne : q ≠ 0 := ne_of_gt hq
  have hWD : torusAmbientFKWeight L (selfDualPoint q) q
      (torusCellDualAmbientConfig L omega) ≠ 0 :=
    ne_of_gt (torusAmbientFKWeight_pos L _ hp hp1 hq)
  rcases torusAmbientDefect_classified L omega with hd | hd | hd
  · left
    rw [hd, zpow_zero, mul_one] at hrel
    field_simp [hqne, hWD]
    simpa [mul_comm] using hrel
  · right; left
    rw [hd, zpow_one] at hrel
    have hw := mul_right_cancel₀ hqne hrel
    rw [hw, div_self hWD]
  · right; right
    rw [hd, zpow_two] at hrel
    have hw : torusAmbientFKWeight L (selfDualPoint q) q omega =
        torusAmbientFKWeight L (selfDualPoint q) q
          (torusCellDualAmbientConfig L omega) * q := by
      apply mul_right_cancel₀ hqne
      simpa [mul_assoc] using hrel
    rw [hw, mul_div_cancel_left₀ _ hWD]


theorem torusAmbientProbability_selfDual_ratio_mem
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {q : ℝ} (hq1 : 1 ≤ q) :
    let ratio := torusAmbientProbability L (selfDualPoint q) q omega /
      torusAmbientProbability L (selfDualPoint q) q
        (torusCellDualAmbientConfig L omega)
    q⁻¹ ≤ ratio ∧ ratio ≤ q := by
  have hq : 0 < q := lt_of_lt_of_le one_pos hq1
  have hinv : q⁻¹ ≤ 1 := (inv_le_one₀ hq).2 hq1
  have hinvq : q⁻¹ ≤ q := hinv.trans hq1
  rcases torusAmbientProbability_selfDual_ratio_values L omega hq with
    hratio | hratio | hratio
  · rw [hratio]
    exact ⟨le_rfl, hinvq⟩
  · rw [hratio]
    exact ⟨hinv, hq1⟩
  · rw [hratio]
    exact ⟨hinvq, le_rfl⟩

end StatMech.BeffaraDC
