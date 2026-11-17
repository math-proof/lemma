/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


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
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

public noncomputable section

structure EvenExponentialTypeImaginaryZeros (F : Complex → Complex) where
  analytic : AnalyticOnNhd Complex F Set.univ
  value_zero_ne : F 0 ≠ 0
  even : ∀ z, F (-z) = F z
  prefactor : Real
  exponentialType : Real
  prefactor_pos : 0 < prefactor
  exponentialType_nonneg : 0 ≤ exponentialType
  norm_le : ∀ z, ‖F z‖ ≤ prefactor * Real.exp (exponentialType * ‖z‖)
  zeros_imaginary : ∀ z, F z = 0 → z.re = 0


end
end StatMech.FrontierA
