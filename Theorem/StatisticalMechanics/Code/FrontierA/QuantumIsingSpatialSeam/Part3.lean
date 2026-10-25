/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part3
open scoped BigOperators


namespace StatMech.FrontierA

theorem quantumIsingSpatialTrotterWeight_le_exp_mul_open
    (beta : Real) (n L : Nat) (hn : n ≠ 0) (hbeta : 0 ≤ beta)
    (sigma : QuantumIsingChainConfig (L + 1)) :
    quantumIsingSpatialTrotterWeight beta n (L + 1) sigma ≤
      Real.exp (beta / (4 * (n : Real))) *
        quantumIsingOpenSpatialTrotterWeight beta n L sigma := by
  let J : Real := beta / (4 * (n : Real))
  have hJ : 0 ≤ J := by
    dsimp [J]
    positivity
  have hdiff := abs_quantumIsingChainInteraction_sub_open L sigma
  have hle : J * (quantumIsingChainInteraction (L + 1) sigma -
      quantumIsingOpenChainInteraction L sigma) ≤ J := by
    have := (abs_le.mp (le_of_eq hdiff)).2
    nlinarith
  unfold quantumIsingSpatialTrotterWeight
  change Real.exp (J * quantumIsingChainInteraction (L + 1) sigma) ≤
    Real.exp J * Real.exp
      (J * quantumIsingOpenChainInteraction L sigma)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith


theorem exp_neg_mul_open_le_quantumIsingSpatialTrotterWeight
    (beta : Real) (n L : Nat) (hn : n ≠ 0) (hbeta : 0 ≤ beta)
    (sigma : QuantumIsingChainConfig (L + 1)) :
    Real.exp (-(beta / (4 * (n : Real)))) *
        quantumIsingOpenSpatialTrotterWeight beta n L sigma ≤
      quantumIsingSpatialTrotterWeight beta n (L + 1) sigma := by
  let J : Real := beta / (4 * (n : Real))
  have hJ : 0 ≤ J := by
    dsimp [J]
    positivity
  have hdiff := abs_quantumIsingChainInteraction_sub_open L sigma
  have hle : -J ≤ J * (quantumIsingChainInteraction (L + 1) sigma -
      quantumIsingOpenChainInteraction L sigma) := by
    have := (abs_le.mp (le_of_eq hdiff)).1
    nlinarith
  unfold quantumIsingSpatialTrotterWeight
  change Real.exp (-J) * Real.exp
      (J * quantumIsingOpenChainInteraction L sigma) ≤
    Real.exp (J * quantumIsingChainInteraction (L + 1) sigma)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith


end StatMech.FrontierA
