/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.DyadicInverseSquareSummability.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.HadamardQuadraticFactorOrder
import Theorem.StatisticalMechanics.Code.FrontierA.EntireOrderMatchedQuotient
import Theorem.StatisticalMechanics.Code.FrontierA.EntireZeroFreeLogarithm
import Theorem.StatisticalMechanics.Code.FrontierA.EntireExponentialLogAffine
import Theorem.StatisticalMechanics.Code.FrontierA.EntireExponentialCharacteristicAffine
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Lindelof
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part8
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem hadamardZeroCountIntercept_nonneg
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    0 ≤ hadamardZeroCountIntercept hF :=
  le_max_left _ _

theorem hadamardZeroCountSlope_nonneg
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    0 ≤ hadamardZeroCountSlope hF := by
  unfold hadamardZeroCountSlope
  exact div_nonneg (mul_nonneg (by norm_num) hF.exponentialType_nonneg)
    (Real.log_pos (by norm_num : (1 : Real) < 2)).le


theorem EvenExponentialTypeImaginaryZeros.card_positiveImaginaryZeroCopiesBelow_le_affine
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 0 < R) :
    (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Real) ≤
      hadamardZeroCountIntercept hF + hadamardZeroCountSlope hF * R := by
  have hj := hF.card_positiveImaginaryZeroCopiesBelow_le_jensen hR
  have hlogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hratio : (2 * R) / R = (2 : Real) := by
    field_simp
  rw [hratio] at hj
  let E : Real := Real.exp (hF.exponentialType * (2 * R))
  have hEpos : 0 < E := Real.exp_pos _
  have hEone : 1 ≤ E := by
    dsimp [E]
    exact Real.one_le_exp (mul_nonneg hF.exponentialType_nonneg (by positivity))
  have hmajorant : hadamardJensenMajorant hF R ≤
      (1 + hF.prefactor) * E := by
    unfold hadamardJensenMajorant
    apply max_le
    · nlinarith [hF.prefactor_pos]
    · nlinarith [hF.prefactor_pos]
  have hnorm : 0 < ‖F 0‖ := norm_pos_iff.mpr hF.value_zero_ne
  have hquotPos : 0 < hadamardJensenMajorant hF R / ‖F 0‖ := by
    exact div_pos (lt_of_lt_of_le zero_lt_one
      (hadamardJensenMajorant_one_le hF R)) hnorm
  have hupperPos : 0 < ((1 + hF.prefactor) * E) / ‖F 0‖ := by
    exact div_pos (mul_pos (by linarith [hF.prefactor_pos]) hEpos) hnorm
  have hlog :
      Real.log (hadamardJensenMajorant hF R / ‖F 0‖) ≤
        Real.log (((1 + hF.prefactor) * E) / ‖F 0‖) := by
    apply Real.strictMonoOn_log.monotoneOn hquotPos hupperPos
    exact div_le_div_of_nonneg_right hmajorant hnorm.le
  have hrewrite :
      Real.log (((1 + hF.prefactor) * E) / ‖F 0‖) =
        Real.log ((1 + hF.prefactor) / ‖F 0‖) +
          2 * hF.exponentialType * R := by
    rw [Real.log_div
        (mul_ne_zero (by linarith [hF.prefactor_pos]) hEpos.ne') hnorm.ne',
      Real.log_mul (by linarith [hF.prefactor_pos] :
        (1 + hF.prefactor) ≠ 0) hEpos.ne']
    dsimp [E]
    rw [Real.log_exp, Real.log_div
      (by linarith [hF.prefactor_pos]) hnorm.ne']
    ring
  rw [hrewrite] at hlog
  calc
    (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Real) ≤
        Real.log (hadamardJensenMajorant hF R / ‖F 0‖) /
          Real.log 2 := hj
    _ ≤ (Real.log ((1 + hF.prefactor) / ‖F 0‖) +
          2 * hF.exponentialType * R) / Real.log 2 :=
      div_le_div_of_nonneg_right hlog hlogTwo.le
    _ ≤ (max 0 (Real.log ((1 + hF.prefactor) / ‖F 0‖) /
          Real.log 2)) +
          (2 * hF.exponentialType / Real.log 2) * R := by
      have hbase : Real.log ((1 + hF.prefactor) / ‖F 0‖) /
          Real.log 2 ≤
          max 0 (Real.log ((1 + hF.prefactor) / ‖F 0‖) /
            Real.log 2) := le_max_right _ _
      rw [add_div]
      have hterm : (2 * hF.exponentialType * R) / Real.log 2 =
          (2 * hF.exponentialType / Real.log 2) * R := by ring
      rw [hterm]
      simpa [add_comm] using add_le_add_right hbase
        ((2 * hF.exponentialType / Real.log 2) * R)
    _ = hadamardZeroCountIntercept hF +
          hadamardZeroCountSlope hF * R := rfl


end
end StatMech.FrontierA
