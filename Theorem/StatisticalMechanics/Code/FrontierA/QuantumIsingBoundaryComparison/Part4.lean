/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part4
open scoped BigOperators


namespace StatMech.FrontierA

theorem quantumIsingBlockLongLayer_le
    (beta h : Real) (n k L : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1))
    (t : Fin (n + 1)) :
    Real.exp (beta / (4 * (n + 1)) *
        quantumIsingBlockLongInteraction k L (omega t)) *
        quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t ≤
      Real.exp (beta * (k + 1) / (2 * (n + 1))) *
        (Real.exp (beta / (4 * (n + 1)) *
          quantumIsingBlockPeriodicInteraction k L (omega t)) *
          quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t) := by
  have hdiff := quantumIsingBlockInteraction_sub_le k L (omega t)
  have hinter : quantumIsingBlockLongInteraction k L (omega t) ≤
      quantumIsingBlockPeriodicInteraction k L (omega t) +
        2 * (k + 1 : Real) := by
    rw [abs_le] at hdiff
    linarith
  have hcoeff : 0 ≤ beta / (4 * (n + 1 : Real)) := by positivity
  have hexp : Real.exp (beta / (4 * (n + 1)) *
        quantumIsingBlockLongInteraction k L (omega t)) ≤
      Real.exp (beta * (k + 1) / (2 * (n + 1))) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingBlockPeriodicInteraction k L (omega t)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    calc
      beta / (4 * (n + 1 : Real)) *
          quantumIsingBlockLongInteraction k L (omega t) ≤
        beta / (4 * (n + 1 : Real)) *
          (quantumIsingBlockPeriodicInteraction k L (omega t) +
            2 * (k + 1 : Real)) :=
        mul_le_mul_of_nonneg_left hinter hcoeff
      _ = beta * (k + 1) / (2 * (n + 1 : Real)) +
          beta / (4 * (n + 1 : Real)) *
            quantumIsingBlockPeriodicInteraction k L (omega t) := by
        field_simp
        ring
  have hvertical : 0 ≤ quantumIsingBlockVerticalLayerWeight beta h
      (n + 1) (k + 1) (L + 1) omega t := by
    unfold quantumIsingBlockVerticalLayerWeight quantumIsingVerticalBondWeight
    positivity
  calc
    _ ≤ (Real.exp (beta * (k + 1) / (2 * (n + 1))) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingBlockPeriodicInteraction k L (omega t))) *
        quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t :=
      mul_le_mul_of_nonneg_right hexp hvertical
    _ = _ := by ring

theorem quantumIsingBlockPeriodicLayer_le
    (beta h : Real) (n k L : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1))
    (t : Fin (n + 1)) :
    Real.exp (beta / (4 * (n + 1)) *
        quantumIsingBlockPeriodicInteraction k L (omega t)) *
        quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t ≤
      Real.exp (beta * (k + 1) / (2 * (n + 1))) *
        (Real.exp (beta / (4 * (n + 1)) *
          quantumIsingBlockLongInteraction k L (omega t)) *
          quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t) := by
  have hdiff := quantumIsingBlockInteraction_sub_le k L (omega t)
  have hinter : quantumIsingBlockPeriodicInteraction k L (omega t) ≤
      quantumIsingBlockLongInteraction k L (omega t) +
        2 * (k + 1 : Real) := by
    rw [abs_le] at hdiff
    linarith
  have hcoeff : 0 ≤ beta / (4 * (n + 1 : Real)) := by positivity
  have hexp : Real.exp (beta / (4 * (n + 1)) *
        quantumIsingBlockPeriodicInteraction k L (omega t)) ≤
      Real.exp (beta * (k + 1) / (2 * (n + 1))) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingBlockLongInteraction k L (omega t)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    calc
      beta / (4 * (n + 1 : Real)) *
          quantumIsingBlockPeriodicInteraction k L (omega t) ≤
        beta / (4 * (n + 1 : Real)) *
          (quantumIsingBlockLongInteraction k L (omega t) +
            2 * (k + 1 : Real)) :=
        mul_le_mul_of_nonneg_left hinter hcoeff
      _ = beta * (k + 1) / (2 * (n + 1 : Real)) +
          beta / (4 * (n + 1 : Real)) *
            quantumIsingBlockLongInteraction k L (omega t) := by
        field_simp
        ring
  have hvertical : 0 ≤ quantumIsingBlockVerticalLayerWeight beta h
      (n + 1) (k + 1) (L + 1) omega t := by
    unfold quantumIsingBlockVerticalLayerWeight quantumIsingVerticalBondWeight
    positivity
  calc
    _ ≤ (Real.exp (beta * (k + 1) / (2 * (n + 1))) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingBlockLongInteraction k L (omega t))) *
        quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t :=
      mul_le_mul_of_nonneg_right hexp hvertical
    _ = _ := by ring


theorem quantumIsingBlockLongCylinderWeight_le
    (beta h : Real) (n k L : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1)) :
    quantumIsingBlockLongCylinderWeight beta h (n + 1) k L omega ≤
      Real.exp (beta * (k + 1) / 2) *
        quantumIsingBlockPeriodicCylinderWeight beta h (n + 1) k L omega := by
  unfold quantumIsingBlockLongCylinderWeight quantumIsingBlockPeriodicCylinderWeight
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ∏ t : Fin (n + 1),
        Real.exp (beta * (k + 1) / (2 * (n + 1))) *
          (Real.exp (beta / (4 * (n + 1)) *
            quantumIsingBlockPeriodicInteraction k L (omega t)) *
            quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t) := by
      apply Finset.prod_le_prod
      · intro t _
        unfold quantumIsingBlockVerticalLayerWeight quantumIsingVerticalBondWeight
        positivity
      · intro t _
        exact quantumIsingBlockLongLayer_le beta h n k L hbeta omega t
    _ = Real.exp (beta * (k + 1) / 2) *
        ∏ t : Fin (n + 1),
          Real.exp (beta / (4 * (n + 1)) *
            quantumIsingBlockPeriodicInteraction k L (omega t)) *
            quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp


theorem quantumIsingBlockPeriodicCylinderWeight_le
    (beta h : Real) (n k L : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1)) :
    quantumIsingBlockPeriodicCylinderWeight beta h (n + 1) k L omega ≤
      Real.exp (beta * (k + 1) / 2) *
        quantumIsingBlockLongCylinderWeight beta h (n + 1) k L omega := by
  unfold quantumIsingBlockLongCylinderWeight quantumIsingBlockPeriodicCylinderWeight
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ∏ t : Fin (n + 1),
        Real.exp (beta * (k + 1) / (2 * (n + 1))) *
          (Real.exp (beta / (4 * (n + 1)) *
            quantumIsingBlockLongInteraction k L (omega t)) *
            quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t) := by
      apply Finset.prod_le_prod
      · intro t _
        unfold quantumIsingBlockVerticalLayerWeight quantumIsingVerticalBondWeight
        positivity
      · intro t _
        exact quantumIsingBlockPeriodicLayer_le beta h n k L hbeta omega t
    _ = Real.exp (beta * (k + 1) / 2) *
        ∏ t : Fin (n + 1),
          Real.exp (beta / (4 * (n + 1)) *
            quantumIsingBlockLongInteraction k L (omega t)) *
            quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp

end StatMech.FrontierA
