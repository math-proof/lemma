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
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part4
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroCopiesBelow_finite
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    (positiveImaginaryZeroCopiesBelow F R).Finite := by
  let location : positiveImaginaryZeroCopies F → Complex :=
    fun q => (q.1.1 : Complex) * Complex.I
  have hzeroDisk :
      (entireZeroSet F ∩ closedBall (0 : Complex) |R|).Finite := by
    exact ((isCompact_closedBall (0 : Complex) |R|).inter_left
        hF.entireZeroSet_closed_discrete.1).finite
          (hF.entireZeroSet_closed_discrete.2.mono Set.inter_subset_left)
  apply Set.Finite.of_finite_fibers location
  · apply hzeroDisk.subset
    rintro z ⟨q, hq, rfl⟩
    constructor
    · exact q.1.2.2
    · rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs]
      rw [abs_of_pos q.1.2.1]
      exact hq.trans (le_abs_self R)
  · intro z
    intro _hz
    rcases (location ⁻¹' {z}).eq_empty_or_nonempty with hempty | ⟨q₀, hq₀⟩
    · simp [hempty]
    · let embed :
          Fin (analyticOrderAt F ((q₀.1.1 : Complex) * Complex.I)).toNat →
            positiveImaginaryZeroCopies F :=
          fun i => ⟨q₀.1, i⟩
      apply (Set.finite_range embed).subset
      intro q hq
      have hloc : location q = location q₀ := by
        exact hq.2.trans hq₀.symm
      have hy : q.1 = q₀.1 := by
        apply Subtype.ext
        have him := congrArg Complex.im hloc
        simpa [location] using him
      cases q with
      | mk y i =>
          cases q₀ with
          | mk y₀ i₀ =>
              dsimp at hy ⊢
              subst y₀
              exact ⟨i, rfl⟩


end
end StatMech.FrontierA
