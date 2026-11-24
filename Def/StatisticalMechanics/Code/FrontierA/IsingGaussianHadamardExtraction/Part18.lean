module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.DyadicInverseSquareSummability.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.HadamardQuadraticFactorOrder
public import Theorem.StatisticalMechanics.Code.FrontierA.EntireOrderMatchedQuotient
public import Theorem.StatisticalMechanics.Code.FrontierA.EntireZeroFreeLogarithm
public import Theorem.StatisticalMechanics.Code.FrontierA.EntireExponentialLogAffine
public import Theorem.StatisticalMechanics.Code.FrontierA.EntireExponentialCharacteristicAffine
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Compactness.Lindelof
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part17
open Filter Metric
open scoped BigOperators ComplexConjugate


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
