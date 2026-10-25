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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part4
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

def entireDiskZeroSet (F : Complex → Complex) (R : Real) : Type :=
  {z : Complex // z ∈ closedBall 0 R ∧ F z = 0}


def entireDiskZeroCopies (F : Complex → Complex) (R : Real) : Type :=
  Σ z : entireDiskZeroSet F R, Fin (analyticOrderNatAt F z.1)

end
end StatMech.FrontierA
