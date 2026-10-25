/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingAgreementGramVarianceCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierA.IsingAgreementGramVarianceCounterexample


namespace StatMech.FrontierA

open scoped BigOperators

noncomputable section

theorem gramVarianceCounterKernel_pos (i j : Fin 3) :
    0 < gramVarianceCounterKernel i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [gramVarianceCounterKernel, gramVarianceCounterDiagonal]

theorem gramVarianceCounterKernel_symm (i j : Fin 3) :
    gramVarianceCounterKernel i j = gramVarianceCounterKernel j i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [gramVarianceCounterKernel, gramVarianceCounterDiagonal]


theorem gramVarianceCounterKernel_quadratic_nonneg (f : Fin 3 -> Real) :
    0 <= ∑ i, ∑ j,
      f i * gramVarianceCounterKernel i j * f j := by
  have h0 : 0 <= (f 0 + f 1 + f 2) ^ 2 := sq_nonneg _
  have h1 : 0 <= f 0 ^ 2 := sq_nonneg _
  have h2 : 0 <= f 1 ^ 2 := sq_nonneg _
  have h3 : 0 <= f 2 ^ 2 := sq_nonneg _
  simp only [Fin.sum_univ_succ]
  norm_num [gramVarianceCounterKernel, gramVarianceCounterDiagonal]
  nlinarith

@[simp] theorem gramVarianceCounterMass_zero :
    gramVarianceCounterMass 0 = 1 := by
  norm_num [gramVarianceCounterMass, gramVarianceCounterKernel,
    gramVarianceCounterDiagonal, Fin.sum_univ_succ]

@[simp] theorem gramVarianceCounterMass_one :
    gramVarianceCounterMass 1 = 8 := by
  norm_num [gramVarianceCounterMass, gramVarianceCounterKernel,
    gramVarianceCounterDiagonal, Fin.sum_univ_succ]

@[simp] theorem gramVarianceCounterMass_two :
    gramVarianceCounterMass 2 = 2 := by
  norm_num [gramVarianceCounterMass, gramVarianceCounterKernel,
    gramVarianceCounterDiagonal, Fin.sum_univ_succ]


theorem gramVarianceCounterMass_compl_ratio_mono
    {i j : Fin 3} (hij : i <= j) :
    gramVarianceCounterMass i *
        gramVarianceCounterMass (gramVarianceCounterReflect j) <=
      gramVarianceCounterMass j *
        gramVarianceCounterMass (gramVarianceCounterReflect i) := by
  fin_cases i <;> fin_cases j
  all_goals simp [gramVarianceCounterReflect, gramVarianceCounterMass,
    gramVarianceCounterKernel, gramVarianceCounterDiagonal,
    Fin.sum_univ_succ] at hij ⊢
  all_goals norm_num

theorem gramVarianceCounterPlusVariance_eq :
    finiteWeightedVariance gramVarianceCounterPlusWeight
      gramVarianceCounterValue = 192 / 175 := by
  norm_num [finiteWeightedVariance, gramVarianceCounterPlusWeight,
    gramVarianceCounterValue, Fin.sum_univ_succ]

theorem gramVarianceCounterMinusVariance_eq :
    finiteWeightedVariance gramVarianceCounterMinusWeight
      gramVarianceCounterValue = 4416 / 4225 := by
  norm_num [finiteWeightedVariance, gramVarianceCounterMinusWeight,
    gramVarianceCounterValue, Fin.sum_univ_succ]


theorem gramVarianceCounterMinusVariance_lt_plus :
    finiteWeightedVariance gramVarianceCounterMinusWeight
        gramVarianceCounterValue <
      finiteWeightedVariance gramVarianceCounterPlusWeight
        gramVarianceCounterValue := by
  rw [gramVarianceCounterPlusVariance_eq,
    gramVarianceCounterMinusVariance_eq]
  norm_num

end
end StatMech.FrontierA
