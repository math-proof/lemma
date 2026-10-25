/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit.Part7
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

theorem quantumIsingClassicalLogPressure_tendsto
    (beta h : Real) (n : Nat) (hbeta : 0 ≤ beta) :
    Tendsto
      (fun L : Nat => quantumIsingClassicalLogPartitionSequence beta h n L / L)
      atTop (nhds (quantumIsingClassicalLogPressureLimit beta h n hbeta)) :=
  (quantumIsingClassicalLogPartitionSequence_almostAdditive beta h n hbeta).tendsto_limit


theorem quantumIsingClassicalLogPressureLimit_sub_finite_le
    (beta h : Real) (n L : Nat) (hbeta : 0 ≤ beta) (hL : L ≠ 0) :
    |quantumIsingClassicalLogPressureLimit beta h n hbeta -
      Real.log (quantumIsingClassicalCylinderPartition beta h (n + 1) L) / L| ≤
        beta / L := by
  have h := (quantumIsingClassicalLogPartitionSequence_almostAdditive
    beta h n hbeta).abs_limit_sub_div_le hL
  simpa [quantumIsingClassicalLogPressureLimit,
    quantumIsingClassicalLogPartitionSequence, hL] using h


theorem quantumIsingClassicalLogPressureLimit_sub_finite_le_sharp
    (beta h : Real) (n L : Nat) (hbeta : 0 ≤ beta) (hL : L ≠ 0) :
    |quantumIsingClassicalLogPressureLimit beta h n hbeta -
      Real.log (quantumIsingClassicalCylinderPartition beta h (n + 1) L) / L| ≤
        beta / (2 * L) := by
  obtain ⟨A, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL
  let Z := fun W => quantumIsingClassicalCylinderPartition beta h (n + 1) W
  have hZ (W : Nat) : 0 < Z W :=
    quantumIsingClassicalCylinderPartition_pos _ _ _ _
  have hfinite (k : Nat) :
      |quantumIsingClassicalLogPartitionSequence beta h n ((k + 1) * (A + 1)) /
          (((k + 1) * (A + 1) : Nat) : Real) -
        Real.log (Z (A + 1)) / (A + 1 : Real)| ≤
          beta / (2 * (A + 1 : Real)) := by
    have hu :=
      quantumIsingClassicalCylinderPartition_block_upper beta h n k A hbeta
    have hl :=
      quantumIsingClassicalCylinderPartition_block_lower beta h n k A hbeta
    have hrep : 0 < Z ((k + 1) * (A + 1)) := hZ _
    have hbase : 0 < Z (A + 1) := hZ _
    have huLog := Real.strictMonoOn_log.monotoneOn hrep
      (mul_pos (pow_pos hbase _) (Real.exp_pos _)) hu
    have hlLog := Real.strictMonoOn_log.monotoneOn
      (mul_pos (pow_pos hbase _) (Real.exp_pos _)) hrep hl
    rw [Real.log_mul (pow_ne_zero _ hbase.ne') (Real.exp_ne_zero _),
      Real.log_pow, Real.log_exp] at huLog hlLog
    have hwidth : (k + 1) * (A + 1) ≠ 0 :=
      Nat.mul_ne_zero (by omega) (by omega)
    simp only [quantumIsingClassicalLogPartitionSequence, hwidth, ↓reduceIte]
    rw [abs_le]
    constructor <;> push_cast at * <;>
      field_simp [show (k : Real) + 1 ≠ 0 by positivity,
        show (A : Real) + 1 ≠ 0 by positivity] at * <;> nlinarith
  have hindex : Tendsto (fun k : Nat => (k + 1) * (A + 1)) atTop atTop := by
    rw [tendsto_atTop]
    intro W
    filter_upwards [eventually_ge_atTop W] with k hk
    nlinarith
  have hpressure := quantumIsingClassicalLogPressure_tendsto beta h n hbeta
  have hsubseq := hpressure.comp hindex
  have hdiff := hsubseq.sub (tendsto_const_nhds : Tendsto
    (fun _ : Nat => Real.log (Z (A + 1)) / (A + 1 : Real)) atTop
      (nhds (Real.log (Z (A + 1)) / (A + 1 : Real))))
  have habs := hdiff.abs
  have hfinal := le_of_tendsto habs (Filter.Eventually.of_forall hfinite)
  simpa [Z, Nat.cast_add, Nat.cast_one] using hfinal

end StatMech.FrontierA
