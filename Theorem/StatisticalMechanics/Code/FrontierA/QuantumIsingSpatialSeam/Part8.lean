/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part8
open scoped BigOperators


namespace StatMech.FrontierA

theorem quantumIsingTrotterThermodynamicFreeEnergy_eq_limit
    (beta h : Real) (n : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h) :
    quantumIsingTrotterThermodynamicFreeEnergy beta h n =
      (quantumIsingOpenTrotterAction_almostAdditive
        beta h n hn hbeta hbh).limit := by
  simp [quantumIsingTrotterThermodynamicFreeEnergy, hn, hbeta, hbh]


theorem quantumIsingPeriodicTrotterFreeEnergy_tendsto
    (beta h : Real) (n : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h) :
    Filter.Tendsto
      (fun L : Nat => quantumIsingPeriodicTrotterAction beta h n L / L)
      Filter.atTop
      (nhds (quantumIsingTrotterThermodynamicFreeEnergy beta h n)) := by
  have hopen := quantumIsingOpenTrotterFreeEnergy_tendsto
    beta h n hn hbeta hbh
  rw [← quantumIsingTrotterThermodynamicFreeEnergy_eq_limit
    beta h n hn hbeta hbh] at hopen
  have herr : Filter.Tendsto (fun L : Nat => (1 / 4 : Real) / L)
      Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (1 / 4 : Real)
  have hdiffAbs : Filter.Tendsto
      (fun L : Nat =>
        |quantumIsingPeriodicTrotterAction beta h n L / L -
          quantumIsingOpenTrotterAction beta h n L / L|)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun L => abs_nonneg _)
      (fun L => ?_) herr
    rw [← sub_div, abs_div]
    nth_rewrite 2 [abs_of_nonneg (Nat.cast_nonneg L)]
    gcongr
    exact abs_quantumIsingPeriodicTrotterAction_sub_open
      beta h n L hn hbeta hbh
  have hdiff : Filter.Tendsto
      (fun L : Nat => quantumIsingPeriodicTrotterAction beta h n L / L -
        quantumIsingOpenTrotterAction beta h n L / L)
      Filter.atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using hdiffAbs
  convert hopen.add hdiff using 1
  · funext L
    ring
  · simp


theorem quantumIsingPeriodicTrotterFreeEnergy_uniform_bound
    (beta h : Real) (n : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h)
    {L : Nat} (hL : L ≠ 0) :
    |quantumIsingTrotterThermodynamicFreeEnergy beta h n -
      quantumIsingPeriodicTrotterAction beta h n L / L| ≤
        1 / (2 * (L : Real)) := by
  rw [quantumIsingTrotterThermodynamicFreeEnergy_eq_limit
    beta h n hn hbeta hbh]
  have hopen := quantumIsingOpenTrotterFreeEnergy_uniform_bound
    beta h n hn hbeta hbh hL
  have hseam := abs_quantumIsingPeriodicTrotterAction_sub_open
    beta h n L hn hbeta hbh
  have hLpos : 0 < (L : Real) := by exact_mod_cast Nat.pos_of_ne_zero hL
  have hseamDiv :
      |quantumIsingOpenTrotterAction beta h n L / L -
        quantumIsingPeriodicTrotterAction beta h n L / L| ≤
          (1 / 4 : Real) / L := by
    rw [← sub_div, abs_div, abs_of_pos hLpos]
    apply div_le_div_of_nonneg_right ?_ hLpos.le
    simpa [abs_sub_comm] using hseam
  calc
    |(quantumIsingOpenTrotterAction_almostAdditive
          beta h n hn hbeta hbh).limit -
        quantumIsingPeriodicTrotterAction beta h n L / L| ≤
      |(quantumIsingOpenTrotterAction_almostAdditive
          beta h n hn hbeta hbh).limit -
        quantumIsingOpenTrotterAction beta h n L / L| +
      |quantumIsingOpenTrotterAction beta h n L / L -
        quantumIsingPeriodicTrotterAction beta h n L / L| :=
      abs_sub_le _ _ _
    _ ≤ (1 / 4 : Real) / L + (1 / 4 : Real) / L :=
      add_le_add hopen hseamDiv
    _ = 1 / (2 * (L : Real)) := by
      field_simp [hL]
      norm_num

end StatMech.FrontierA
