/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part7
open scoped BigOperators


namespace StatMech.FrontierA

theorem quantumIsingTrotterPathPartition_pos
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h) :
    0 < quantumIsingTrotterPathPartition beta h n (L + 1) := by
  have hopen := quantumIsingOpenTrotterPathPartition_pos beta h n L hn hbh
  have hlower := exp_neg_mul_open_le_quantumIsingTrotterPathPartition
    beta h n L hn hbeta.le hbh.le
  exact (mul_pos (Real.exp_pos _) hopen).trans_le hlower


theorem abs_quantumIsingPeriodicTrotterAction_sub_open
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h) :
    |quantumIsingPeriodicTrotterAction beta h n L -
      quantumIsingOpenTrotterAction beta h n L| ≤ 1 / 4 := by
  rcases L with _ | L
  · simp [quantumIsingPeriodicTrotterAction, quantumIsingOpenTrotterAction]
  let Zopen := quantumIsingOpenTrotterPathPartition beta h n L
  let Zper := quantumIsingTrotterPathPartition beta h n (L + 1)
  have hopen : 0 < Zopen :=
    quantumIsingOpenTrotterPathPartition_pos beta h n L hn hbh
  have hper : 0 < Zper :=
    quantumIsingTrotterPathPartition_pos beta h n L hn hbeta hbh
  have hlower : Real.exp (-(beta / 4)) * Zopen ≤ Zper :=
    exp_neg_mul_open_le_quantumIsingTrotterPathPartition
      beta h n L hn hbeta.le hbh.le
  have hupper : Zper ≤ Real.exp (beta / 4) * Zopen :=
    quantumIsingTrotterPathPartition_le_exp_mul_open
      beta h n L hn hbeta.le hbh.le
  have hlogLower := Real.log_le_log
    (mul_pos (Real.exp_pos _) hopen) hlower
  have hlogUpper := Real.log_le_log hper hupper
  rw [Real.log_mul (Real.exp_ne_zero _) hopen.ne', Real.log_exp] at hlogLower hlogUpper
  have hnum : |Real.log Zopen - Real.log Zper| ≤ beta / 4 := by
    rw [abs_le]
    constructor <;> linarith
  simp only [quantumIsingPeriodicTrotterAction,
    quantumIsingOpenTrotterAction]
  rw [show -Real.log Zper / beta - -Real.log Zopen / beta =
      (Real.log Zopen - Real.log Zper) / beta by ring]
  rw [abs_div, abs_of_pos hbeta]
  calc
    |Real.log Zopen - Real.log Zper| / beta ≤ (beta / 4) / beta := by gcongr
    _ = 1 / 4 := by field_simp [hbeta.ne']


end StatMech.FrontierA
