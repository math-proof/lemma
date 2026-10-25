/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit.Part6
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

theorem quantumIsingClassicalLogPartitionSequence_almostAdditive
    (beta h : Real) (n : Nat) (hbeta : 0 ≤ beta) :
    QuantumIsingAlmostAdditive
      (quantumIsingClassicalLogPartitionSequence beta h n) beta := by
  intro m l
  rcases m.eq_zero_or_pos with rfl | hm
  · simpa [quantumIsingClassicalLogPartitionSequence] using hbeta
  rcases l.eq_zero_or_pos with rfl | hl
  · simpa [quantumIsingClassicalLogPartitionSequence] using hbeta
  obtain ⟨A, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨B, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  simp only [quantumIsingClassicalLogPartitionSequence, Nat.add_eq_zero_iff,
    Nat.succ_ne_zero, false_and, ↓reduceIte]
  let ZA := quantumIsingClassicalCylinderPartition beta h (n + 1) (A + 1)
  let ZB := quantumIsingClassicalCylinderPartition beta h (n + 1) (B + 1)
  let ZAB := quantumIsingClassicalCylinderPartition beta h (n + 1) ((A + 1) + (B + 1))
  have hZA : 0 < ZA := quantumIsingClassicalCylinderPartition_pos _ _ _ _
  have hZB : 0 < ZB := quantumIsingClassicalCylinderPartition_pos _ _ _ _
  have hZAB : 0 < ZAB := quantumIsingClassicalCylinderPartition_pos _ _ _ _
  have hu := quantumIsingClassicalCylinderPartition_add_upper beta h n A B hbeta
  have hlower := quantumIsingClassicalCylinderPartition_add_lower beta h n A B hbeta
  change |Real.log ZAB - Real.log ZA - Real.log ZB| ≤ beta
  rw [abs_le]
  constructor
  · have hlog := Real.strictMonoOn_log.monotoneOn
        (mul_pos (Real.exp_pos _) (mul_pos hZA hZB)) hZAB hlower
    rw [Real.log_mul (Real.exp_ne_zero _) (mul_ne_zero hZA.ne' hZB.ne'),
      Real.log_exp, Real.log_mul hZA.ne' hZB.ne'] at hlog
    linarith
  · have hlog := Real.strictMonoOn_log.monotoneOn hZAB
        (mul_pos (Real.exp_pos _) (mul_pos hZA hZB)) hu
    rw [Real.log_mul (Real.exp_ne_zero _) (mul_ne_zero hZA.ne' hZB.ne'),
      Real.log_exp, Real.log_mul hZA.ne' hZB.ne'] at hlog
    linarith


end StatMech.FrontierA
