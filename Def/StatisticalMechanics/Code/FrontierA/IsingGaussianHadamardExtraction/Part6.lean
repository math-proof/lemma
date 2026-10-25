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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part5
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

def positiveImaginaryZeroCopiesBelowToDisk
    {F : Complex → Complex} {R : Real} (hR : 0 ≤ R) :
    positiveImaginaryZeroCopiesBelow F R → entireDiskZeroCopies F R :=
  fun q => ⟨⟨(q.1.1.1 : Complex) * Complex.I, by
    constructor
    · rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_of_pos q.1.1.2.1]
      exact q.2
    · exact q.1.1.2.2⟩, q.1.2⟩

end
end StatMech.FrontierA
