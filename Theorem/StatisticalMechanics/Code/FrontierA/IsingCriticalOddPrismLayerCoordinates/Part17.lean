/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part17


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem two_mul_finiteExpVarianceNumerator_eq_pairSum
    {E : Type*} [Fintype E] (w I : E -> Real) (r : Real) :
    2 * (finiteExpSecond w I r * finiteExpMoment w I r -
      finiteExpFirst w I r ^ 2) =
      ∑ x, ∑ y, w x * w y *
        ((I x - I y) ^ 2 * Real.exp (r * (I x + I y))) := by
  rw [show 2 * (finiteExpSecond w I r * finiteExpMoment w I r -
        finiteExpFirst w I r ^ 2) =
      finiteExpSecond w I r * finiteExpMoment w I r +
        finiteExpMoment w I r * finiteExpSecond w I r -
        2 * (finiteExpFirst w I r * finiteExpFirst w I r) by ring]
  unfold finiteExpMoment finiteExpFirst finiteExpSecond
  have hexp (x y : E) : Real.exp (r * (I x + I y)) =
      Real.exp (r * I x) * Real.exp (r * I y) := by
    rw [show r * (I x + I y) = r * I x + r * I y by ring,
      Real.exp_add]
  simp_rw [hexp]
  simp only [pow_two]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring


theorem two_mul_finiteExpVarianceSkew_eq_fourStateSum
    {E : Type*} [Fintype E] (w I : E -> Real) (r : Real) :
    2 * finiteExpVarianceSkew w I r =
      ∑ x, ∑ y, ∑ z, ∑ q,
        w x * w y * w z * w q * (I x - I y) ^ 2 *
          (Real.exp (r * (I x + I y - I z - I q)) -
            Real.exp (-r * (I x + I y - I z - I q))) := by
  unfold finiteExpVarianceSkew
  rw [show 2 *
      ((finiteExpSecond w I r * finiteExpMoment w I r -
          finiteExpFirst w I r ^ 2) * finiteExpMoment w I (-r) ^ 2 -
        (finiteExpSecond w I (-r) * finiteExpMoment w I (-r) -
          finiteExpFirst w I (-r) ^ 2) * finiteExpMoment w I r ^ 2) =
      (2 * (finiteExpSecond w I r * finiteExpMoment w I r -
          finiteExpFirst w I r ^ 2)) * finiteExpMoment w I (-r) ^ 2 -
        (2 * (finiteExpSecond w I (-r) * finiteExpMoment w I (-r) -
          finiteExpFirst w I (-r) ^ 2)) * finiteExpMoment w I r ^ 2 by ring]
  rw [two_mul_finiteExpVarianceNumerator_eq_pairSum,
    two_mul_finiteExpVarianceNumerator_eq_pairSum]
  unfold finiteExpMoment
  simp only [pow_two]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hp (x y z q : E) : Real.exp (r * (I x + I y)) *
      (Real.exp (-r * I z) * Real.exp (-r * I q)) =
      Real.exp (r * (I x + I y - I z - I q)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hm (x y z q : E) : Real.exp (-r * (I x + I y)) *
      (Real.exp (r * I z) * Real.exp (r * I q)) =
      Real.exp (-r * (I x + I y - I z - I q)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro q _
  calc
    w x * w y * ((I x - I y) * (I x - I y) *
          Real.exp (r * (I x + I y))) *
          (w z * Real.exp (-r * I z) * (w q * Real.exp (-r * I q))) -
        w x * w y * ((I x - I y) * (I x - I y) *
          Real.exp (-r * (I x + I y))) *
          (w z * Real.exp (r * I z) * (w q * Real.exp (r * I q))) =
      w x * w y * w z * w q * ((I x - I y) * (I x - I y)) *
        (Real.exp (r * (I x + I y)) *
            (Real.exp (-r * I z) * Real.exp (-r * I q)) -
          Real.exp (-r * (I x + I y)) *
            (Real.exp (r * I z) * Real.exp (r * I q))) := by ring
    _ = _ := by rw [hp, hm]

end
end StatMech.FrontierA
