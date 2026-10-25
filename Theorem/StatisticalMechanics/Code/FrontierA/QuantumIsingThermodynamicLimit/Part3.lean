/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit.Part3
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

theorem quantumIsingTwoBlockLongLayer_le
    (beta h : Real) (n A B : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1))
    (t : Fin (n + 1)) :
    Real.exp (beta / (4 * (n + 1)) *
        quantumIsingTwoBlockLongInteraction A B (omega t)) *
        quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t ≤
      Real.exp (beta / (n + 1)) *
        (Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockPeriodicInteraction A B (omega t)) *
          quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t) := by
  have hdiff := quantumIsingTwoBlockInteraction_sub_le A B (omega t)
  have hinter : quantumIsingTwoBlockLongInteraction A B (omega t) ≤
      quantumIsingTwoBlockPeriodicInteraction A B (omega t) + 4 := by
    rw [abs_le] at hdiff
    linarith
  have hc : 0 ≤ beta / (4 * (n + 1 : Real)) := by positivity
  have hexp : Real.exp (beta / (4 * (n + 1)) *
      quantumIsingTwoBlockLongInteraction A B (omega t)) ≤
      Real.exp (beta / (n + 1)) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockPeriodicInteraction A B (omega t)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    calc
      _ ≤ beta / (4 * (n + 1 : Real)) *
          (quantumIsingTwoBlockPeriodicInteraction A B (omega t) + 4) :=
        mul_le_mul_of_nonneg_left hinter hc
      _ = _ := by field_simp; ring
  have hv : 0 ≤ quantumIsingTwoBlockVerticalLayerWeight beta h
      (n + 1) (A + 1) (B + 1) omega t := by
    unfold quantumIsingTwoBlockVerticalLayerWeight quantumIsingVerticalBondWeight
    positivity
  calc
    _ ≤ (Real.exp (beta / (n + 1)) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockPeriodicInteraction A B (omega t))) *
        quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t :=
      mul_le_mul_of_nonneg_right hexp hv
    _ = _ := by ring

theorem quantumIsingTwoBlockPeriodicLayer_le
    (beta h : Real) (n A B : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1))
    (t : Fin (n + 1)) :
    Real.exp (beta / (4 * (n + 1)) *
        quantumIsingTwoBlockPeriodicInteraction A B (omega t)) *
        quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t ≤
      Real.exp (beta / (n + 1)) *
        (Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockLongInteraction A B (omega t)) *
          quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t) := by
  have hdiff := quantumIsingTwoBlockInteraction_sub_le A B (omega t)
  have hinter : quantumIsingTwoBlockPeriodicInteraction A B (omega t) ≤
      quantumIsingTwoBlockLongInteraction A B (omega t) + 4 := by
    rw [abs_le] at hdiff
    linarith
  have hc : 0 ≤ beta / (4 * (n + 1 : Real)) := by positivity
  have hexp : Real.exp (beta / (4 * (n + 1)) *
      quantumIsingTwoBlockPeriodicInteraction A B (omega t)) ≤
      Real.exp (beta / (n + 1)) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockLongInteraction A B (omega t)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    calc
      _ ≤ beta / (4 * (n + 1 : Real)) *
          (quantumIsingTwoBlockLongInteraction A B (omega t) + 4) :=
        mul_le_mul_of_nonneg_left hinter hc
      _ = _ := by field_simp; ring
  have hv : 0 ≤ quantumIsingTwoBlockVerticalLayerWeight beta h
      (n + 1) (A + 1) (B + 1) omega t := by
    unfold quantumIsingTwoBlockVerticalLayerWeight quantumIsingVerticalBondWeight
    positivity
  calc
    _ ≤ (Real.exp (beta / (n + 1)) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockLongInteraction A B (omega t))) *
        quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t :=
      mul_le_mul_of_nonneg_right hexp hv
    _ = _ := by ring

theorem quantumIsingTwoBlockLongCylinderWeight_le
    (beta h : Real) (n A B : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1)) :
    quantumIsingTwoBlockLongCylinderWeight beta h (n + 1) A B omega ≤
      Real.exp beta *
        quantumIsingTwoBlockPeriodicCylinderWeight beta h (n + 1) A B omega := by
  unfold quantumIsingTwoBlockLongCylinderWeight quantumIsingTwoBlockPeriodicCylinderWeight
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ∏ t : Fin (n + 1), Real.exp (beta / (n + 1)) *
        (Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockPeriodicInteraction A B (omega t)) *
          quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t) := by
      apply Finset.prod_le_prod
      · intro t _
        unfold quantumIsingTwoBlockVerticalLayerWeight quantumIsingVerticalBondWeight
        positivity
      · intro t _
        exact quantumIsingTwoBlockLongLayer_le beta h n A B hbeta omega t
    _ = Real.exp beta * ∏ t : Fin (n + 1),
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockPeriodicInteraction A B (omega t)) *
          quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp

theorem quantumIsingTwoBlockPeriodicCylinderWeight_le
    (beta h : Real) (n A B : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1)) :
    quantumIsingTwoBlockPeriodicCylinderWeight beta h (n + 1) A B omega ≤
      Real.exp beta *
        quantumIsingTwoBlockLongCylinderWeight beta h (n + 1) A B omega := by
  unfold quantumIsingTwoBlockLongCylinderWeight quantumIsingTwoBlockPeriodicCylinderWeight
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ∏ t : Fin (n + 1), Real.exp (beta / (n + 1)) *
        (Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockLongInteraction A B (omega t)) *
          quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t) := by
      apply Finset.prod_le_prod
      · intro t _
        unfold quantumIsingTwoBlockVerticalLayerWeight quantumIsingVerticalBondWeight
        positivity
      · intro t _
        exact quantumIsingTwoBlockPeriodicLayer_le beta h n A B hbeta omega t
    _ = Real.exp beta * ∏ t : Fin (n + 1),
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockLongInteraction A B (omega t)) *
          quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp


end StatMech.FrontierA
