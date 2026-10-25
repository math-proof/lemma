/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryCompactAverage.Part2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Hull
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryHolderDerivative


namespace StatMech.Universality

open Set Metric

noncomputable section

theorem lagrangeShrinkingTwoPointPosition_injective (k : Nat) :
    Function.Injective (lagrangeShrinkingTwoPointPosition k) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    have hk : ((k : Complex) + 1) ≠ 0 := by
      exact_mod_cast (show k + 1 ≠ 0 by omega)
    apply hk
    simpa [lagrangeShrinkingTwoPointPosition] using hij.symm
  · exfalso
    have hk : ((k : Complex) + 1) ≠ 0 := by
      exact_mod_cast (show k + 1 ≠ 0 by omega)
    apply hk
    simpa [lagrangeShrinkingTwoPointPosition] using hij
  · rfl

theorem lagrangeShrinkingTwoPointValue_norm_le_one (i : Fin 2) :
    ‖lagrangeShrinkingTwoPointValue i‖ ≤ 1 := by
  fin_cases i <;> simp [lagrangeShrinkingTwoPointValue]

theorem lagrangeShrinkingTwoPointPosition_dist (k : Nat) :
    dist (lagrangeShrinkingTwoPointPosition k 0)
        (lagrangeShrinkingTwoPointPosition k 1) =
      1 / (k + 1 : Nat) := by
  change dist (0 : Complex) (((k + 1 : Nat) : Complex)⁻¹) =
    1 / ((k + 1 : Nat) : Real)
  rw [dist_eq_norm, zero_sub, norm_neg, norm_inv, Complex.norm_natCast]
  simp [div_eq_mul_inv]


theorem lagrangeShrinkingTwoPointInterpolant_eq (k : Nat) (z : Complex) :
    finiteLagrangeInterpolant (lagrangeShrinkingTwoPointPosition k)
      lagrangeShrinkingTwoPointValue z =
        ((k + 1 : Nat) : Complex) * z := by
  have herase0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have herase1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  rw [finiteLagrangeInterpolant, Fin.sum_univ_two]
  simp only [finiteLagrangeBasis, herase0, herase1]
  simp [lagrangeShrinkingTwoPointPosition, lagrangeShrinkingTwoPointValue]
  field_simp

theorem lagrangeShrinkingTwoPointInterpolant_deriv (k : Nat) (z : Complex) :
    deriv (finiteLagrangeInterpolant (lagrangeShrinkingTwoPointPosition k)
      lagrangeShrinkingTwoPointValue) z =
        ((k + 1 : Nat) : Complex) := by
  have hfun : finiteLagrangeInterpolant (lagrangeShrinkingTwoPointPosition k)
      lagrangeShrinkingTwoPointValue =
        fun w : Complex ↦ ((k + 1 : Nat) : Complex) * w := by
    funext w
    exact lagrangeShrinkingTwoPointInterpolant_eq k w
  rw [hfun]
  simpa only [id_eq, mul_one] using
    ((hasDerivAt_id z).const_mul ((k + 1 : Nat) : Complex)).deriv

theorem lagrangeShrinkingTwoPointPosition_zero_mem_convexHull (k : Nat) :
    (0 : Complex) ∈
      convexHull Real (Set.range (lagrangeShrinkingTwoPointPosition k)) := by
  apply subset_convexHull Real
  exact ⟨0, by simp [lagrangeShrinkingTwoPointPosition]⟩


theorem lagrangeShrinkingTwoPoint_no_uniform_derivative_bound :
    ¬ ∃ C : NNReal, ∀ k z,
      z ∈ convexHull Real
        (Set.range (lagrangeShrinkingTwoPointPosition k)) →
      ‖deriv (finiteLagrangeInterpolant (lagrangeShrinkingTwoPointPosition k)
        lagrangeShrinkingTwoPointValue) z‖₊ ≤ C := by
  rintro ⟨C, hC⟩
  let k := Nat.ceil C + 1
  have hbound := hC k 0
    (lagrangeShrinkingTwoPointPosition_zero_mem_convexHull k)
  rw [lagrangeShrinkingTwoPointInterpolant_deriv] at hbound
  have hnorm : ‖((k + 1 : Nat) : Complex)‖₊ =
      ((k + 1 : Nat) : NNReal) := by
    apply NNReal.eq
    exact Complex.norm_natCast (k + 1)
  rw [hnorm] at hbound
  have hceil : (C : Real) ≤ Nat.ceil C := Nat.le_ceil C
  have hboundReal : ((k + 1 : Nat) : Real) ≤ (C : Real) := by
    exact_mod_cast hbound
  simp only [k, Nat.cast_add, Nat.cast_one] at hboundReal
  nlinarith


end
end StatMech.Universality
