/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part6
open scoped BigOperators


namespace StatMech.FrontierA

theorem quantumIsingOpenTrotterAction_almostAdditive
    (beta h : Real) (n : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h) :
    QuantumIsingAlmostAdditive (quantumIsingOpenTrotterAction beta h n) (1 / 4) := by
  intro a b
  rcases a with _ | L
  · simp [quantumIsingOpenTrotterAction]
  rcases b with _ | M
  · simp [quantumIsingOpenTrotterAction]
  let ZL := quantumIsingOpenTrotterPathPartition beta h n L
  let ZM := quantumIsingOpenTrotterPathPartition beta h n M
  let ZLM := quantumIsingOpenTrotterPathPartition beta h n (L + M + 1)
  have hZL : 0 < ZL := quantumIsingOpenTrotterPathPartition_pos beta h n L hn hbh
  have hZM : 0 < ZM := quantumIsingOpenTrotterPathPartition_pos beta h n M hn hbh
  have hZLM : 0 < ZLM :=
    quantumIsingOpenTrotterPathPartition_pos beta h n (L + M + 1) hn hbh
  have hlower : Real.exp (-(beta / 4)) * (ZL * ZM) ≤ ZLM :=
    quantumIsing_exp_mul_openPartitions_le_add beta h n L M hn hbeta.le hbh.le
  have hupper : ZLM ≤ Real.exp (beta / 4) * (ZL * ZM) :=
    quantumIsingOpenTrotterPathPartition_add_le beta h n L M hn hbeta.le hbh.le
  have hlogLower := Real.log_le_log
    (mul_pos (Real.exp_pos _) (mul_pos hZL hZM)) hlower
  have hlogUpper := Real.log_le_log hZLM hupper
  rw [Real.log_mul (Real.exp_ne_zero _) (mul_ne_zero hZL.ne' hZM.ne'),
    Real.log_exp, Real.log_mul hZL.ne' hZM.ne'] at hlogLower hlogUpper
  have hnum : |Real.log ZL + Real.log ZM - Real.log ZLM| ≤ beta / 4 := by
    rw [abs_le]
    constructor <;> linarith
  rw [show L + 1 + (M + 1) = (L + M + 1) + 1 by omega]
  simp only [quantumIsingOpenTrotterAction]
  change |(-Real.log ZLM / beta) - (-Real.log ZL / beta) -
    (-Real.log ZM / beta)| ≤ 1 / 4
  rw [show -Real.log ZLM / beta - -Real.log ZL / beta -
      -Real.log ZM / beta =
      (Real.log ZL + Real.log ZM - Real.log ZLM) / beta by ring]
  rw [abs_div, abs_of_pos hbeta]
  calc
    |Real.log ZL + Real.log ZM - Real.log ZLM| / beta ≤
        (beta / 4) / beta := by gcongr
    _ = 1 / 4 := by field_simp [hbeta.ne']


theorem quantumIsingOpenTrotterFreeEnergy_tendsto
    (beta h : Real) (n : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h) :
    Filter.Tendsto
      (fun L : Nat => quantumIsingOpenTrotterAction beta h n L / L)
      Filter.atTop
      (nhds ((quantumIsingOpenTrotterAction_almostAdditive
        beta h n hn hbeta hbh).limit)) :=
  (quantumIsingOpenTrotterAction_almostAdditive
    beta h n hn hbeta hbh).tendsto_limit


theorem quantumIsingOpenTrotterFreeEnergy_uniform_bound
    (beta h : Real) (n : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h)
    {L : Nat} (hL : L ≠ 0) :
    |(quantumIsingOpenTrotterAction_almostAdditive
        beta h n hn hbeta hbh).limit -
      quantumIsingOpenTrotterAction beta h n L / L| ≤
        (1 / 4 : Real) / L :=
  (quantumIsingOpenTrotterAction_almostAdditive
    beta h n hn hbeta hbh).abs_limit_sub_div_le hL


end StatMech.FrontierA
