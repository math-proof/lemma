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
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part15
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

noncomputable def EvenExponentialTypeImaginaryZeros.positiveZeroCopy
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {y : Real} (hy : 0 < y) (hzero : F ((y : Complex) * Complex.I) = 0) :
    positiveImaginaryZeroCopies F := by
  let y₀ : positiveImaginaryZeroSet F := ⟨y, hy, hzero⟩
  have hfinite := hF.analyticOrderAt_ne_top ((y : Complex) * Complex.I)
  have horder : analyticOrderAt F ((y : Complex) * Complex.I) ≠ 0 :=
    (hF.analytic ((y : Complex) * Complex.I) (Set.mem_univ _)).analyticOrderAt_ne_zero.mpr
      hzero
  have hnat : analyticOrderNatAt F ((y : Complex) * Complex.I) ≠ 0 := by
    intro hn
    have hcast := Nat.cast_analyticOrderNatAt hfinite
    rw [hn] at hcast
    exact horder (by simpa using hcast.symm)
  exact ⟨y₀, ⟨0, Nat.pos_of_ne_zero hnat⟩⟩

end
end StatMech.FrontierA
