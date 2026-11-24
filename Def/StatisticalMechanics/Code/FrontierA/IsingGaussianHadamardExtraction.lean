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
public import Structure.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction
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

def entireZeroSet (F : Complex → Complex) : Set Complex :=
  {z | F z = 0}


def positiveImaginaryZeroSet (F : Complex → Complex) : Set Real :=
  {y | 0 < y ∧ F (y * Complex.I) = 0}

end
end StatMech.FrontierA
