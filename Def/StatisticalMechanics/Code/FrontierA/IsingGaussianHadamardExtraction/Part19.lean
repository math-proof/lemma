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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part18
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

def EvenExponentialTypeImaginaryZeros.factorization
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    EvenHadamardFactorization F where
  roots := extractedHadamardRoots hF
  roots_nonneg := extractedHadamardRoots_nonneg hF
  roots_summable := hF.extractedHadamardRoots_summable
  value_zero_ne := hF.value_zero_ne
  normalized_eq := fun z => by
    have hmul := hF.extractedHadamardQuotient_mul_eq z
    rw [hF.extractedHadamardQuotient_eq_zeroValue z] at hmul
    rw [div_eq_iff hF.value_zero_ne]
    simpa [mul_comm] using hmul.symm

section FiniteIsingInput

open StatMech.Ising StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteIsingWeightedFieldPartition_extractionData
    {beta : Real} (hbeta : 0 ≤ beta)
    (a : V → Real) (ha : ∀ v, 0 < a v) :
    EvenExponentialTypeImaginaryZeros
      (finiteIsingWeightedFieldPartition G beta a) where
  analytic := finiteIsingWeightedFieldPartition_analyticOnNhd G beta a
  value_zero_ne := Complex.ne_zero_of_re_pos
    (finiteIsingWeightedFieldPartition_zero_re_pos G beta a)
  even := finiteIsingWeightedFieldPartition_neg G beta a
  prefactor := ∑ s : ConfigSpace V, zeroFieldInteractionWeight G beta s
  exponentialType := finiteIsingWeightedFieldRadius a
  prefactor_pos := by
    have hzero := finiteIsingWeightedFieldPartition_zero_re_pos G beta a
    rw [finiteIsingWeightedFieldPartition_zero] at hzero
    simpa using hzero
  exponentialType_nonneg := finiteIsingWeightedFieldRadius_nonneg a
  norm_le := fun z => by
    simpa [mul_comm] using norm_finiteIsingWeightedFieldPartition_le G beta a z
  zeros_imaginary := fun z hz => by
    by_contra hre
    exact finiteIsingWeightedFieldPartition_ne_zero_of_re_ne_zero
      G hbeta a ha hre hz


def finiteIsingWeightedFieldPartition_factorization
    {beta : Real} (hbeta : 0 ≤ beta)
    (a : V → Real) (ha : ∀ v, 0 < a v) :
    FiniteIsingWeightedHadamardFactorization (G := G) beta a :=
  (finiteIsingWeightedFieldPartition_extractionData G hbeta a ha).factorization

end FiniteIsingInput
end
end StatMech.FrontierA
