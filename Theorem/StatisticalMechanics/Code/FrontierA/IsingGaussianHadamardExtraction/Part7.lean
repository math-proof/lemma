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
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part7
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem hadamardJensenMajorant_one_le
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    1 ≤ hadamardJensenMajorant hF R :=
  le_max_left _ _


theorem EvenExponentialTypeImaginaryZeros.zeroMultiplicity_finsum_le
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 0 < R) :
    ((∑ᶠ z : Complex,
      (MeromorphicOn.divisor F (closedBall 0 R)) z : Int) : Real) ≤
      Real.log (hadamardJensenMajorant hF R / ‖F 0‖) /
        Real.log ((2 * R) / R) := by
  have hbound : ∀ z ∈ sphere (0 : Complex) |2 * R|,
      ‖F z‖ ≤ hadamardJensenMajorant hF R := by
    intro z hz
    have hnorm : ‖z‖ = 2 * R := by
      simpa [abs_of_pos (by positivity : 0 < 2 * R)] using hz
    calc
      ‖F z‖ ≤ hF.prefactor *
          Real.exp (hF.exponentialType * ‖z‖) := hF.norm_le z
      _ = hF.prefactor *
          Real.exp (hF.exponentialType * (2 * R)) := by rw [hnorm]
      _ ≤ hadamardJensenMajorant hF R :=
        le_max_right _ _
  have hj := AnalyticOnNhd.sum_divisor_le
    (c := (0 : Complex)) (r := R) (R := 2 * R)
    (M := hadamardJensenMajorant hF R)
    (by simpa [abs_of_pos hR] using hR)
    (by rw [abs_of_pos hR,
      abs_of_pos (by positivity : 0 < 2 * R)]; linarith)
    (hadamardJensenMajorant_one_le hF R)
    (hF.analytic.mono (Set.subset_univ _)) hF.value_zero_ne hbound
  rw [abs_of_pos hR] at hj
  exact hj

theorem EvenExponentialTypeImaginaryZeros.card_positiveImaginaryZeroCopiesBelow_le_jensen
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 0 < R) :
    (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Real) ≤
      Real.log (hadamardJensenMajorant hF R / ‖F 0‖) /
        Real.log ((2 * R) / R) := by
  have hcardInt := hF.card_positiveImaginaryZeroCopiesBelow_le_divisor hR.le
  have hcardReal :
      (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Real) ≤
        ((∑ᶠ z : Complex,
          (MeromorphicOn.divisor F (closedBall 0 R)) z : Int) : Real) := by
    exact_mod_cast hcardInt
  exact hcardReal.trans (hF.zeroMultiplicity_finsum_le hR)


end
end StatMech.FrontierA
