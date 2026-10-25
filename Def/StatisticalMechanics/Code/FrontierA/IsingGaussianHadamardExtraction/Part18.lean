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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part17
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

def EvenExponentialTypeImaginaryZeros.factorization_of_quotient_growth
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {A B : Real} (hA : 0 < A) (hB : 0 ≤ B)
    (hgrowth : ∀ z,
      ‖extractedHadamardQuotient hF z‖ ≤ A * Real.exp (B * ‖z‖)) :
    EvenHadamardFactorization F where
  roots := extractedHadamardRoots hF
  roots_nonneg := extractedHadamardRoots_nonneg hF
  roots_summable := hF.extractedHadamardRoots_summable
  value_zero_ne := hF.value_zero_ne
  normalized_eq := fun z => by
    have hmul := hF.extractedHadamardQuotient_mul_eq z
    rw [hF.extractedHadamardQuotient_eq_zeroValue_of_growth hA hB hgrowth z]
      at hmul
    rw [div_eq_iff hF.value_zero_ne]
    simpa [mul_comm] using hmul.symm


end
end StatMech.FrontierA
