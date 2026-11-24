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
public import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction
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

theorem EvenExponentialTypeImaginaryZeros.entireZeroSet_countable
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    (entireZeroSet F).Countable := by
  have hcodiscrete : (entireZeroSet F)ᶜ ∈ Filter.codiscrete Complex := by
    simpa [entireZeroSet] using
      hF.analytic.preimage_zero_mem_codiscrete hF.value_zero_ne
  have hclosed_discrete := compl_mem_codiscrete_iff.mp hcodiscrete
  exact (isLindelof_univ.of_isClosed_subset hclosed_discrete.1
    (Set.subset_univ _)).countable_of_isDiscrete hclosed_discrete.2

theorem EvenExponentialTypeImaginaryZeros.entireZeroSet_closed_discrete
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    IsClosed (entireZeroSet F) ∧ IsDiscrete (entireZeroSet F) := by
  apply compl_mem_codiscrete_iff.mp
  simpa [entireZeroSet] using
    hF.analytic.preimage_zero_mem_codiscrete hF.value_zero_ne

theorem EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroSet_countable
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    (positiveImaginaryZeroSet F).Countable := by
  have hsubset : positiveImaginaryZeroSet F ⊆
      (fun z : Complex => z.im) '' entireZeroSet F := by
    intro y hy
    refine ⟨y * Complex.I, ?_, ?_⟩
    · exact hy.2
    · simp
  exact (hF.entireZeroSet_countable.image _).mono hsubset


end
end StatMech.FrontierA
