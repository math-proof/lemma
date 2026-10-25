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
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part14
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

@[simp] theorem mem_hadamardVanishingIndices
    {roots : Nat → Real} (hsum : Summable roots) (z : Complex) (n : Nat) :
    n ∈ hadamardVanishingIndices hsum z ↔
      hadamardRootFactor roots n z = 0 := by
  simp [hadamardVanishingIndices]

theorem hasProdLocallyUniformlyOn_hadamardQuadraticFactor
    {ι : Type*} {r : ι → Real} (hr : ∀ i, 0 ≤ r i)
    (hsum : Summable r) :
    HasProdLocallyUniformlyOn (fun i z => hadamardQuadraticFactor (r i) z)
      (fun z => ∏' i, hadamardQuadraticFactor (r i) z) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _hK hcompact
  rcases K.eq_empty_or_nonempty with rfl | hnonempty
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using
      tendstoUniformlyOn_empty
  · obtain ⟨z₀, hz₀, _hmaxEq, hmax⟩ :=
      hcompact.exists_sSup_image_eq_and_ge hnonempty
        (show ContinuousOn (fun z : Complex => ‖z‖ ^ 2) K by fun_prop)
    let u : ι → Real := fun i => r i * ‖z₀‖ ^ 2
    have hu : Summable u := hsum.mul_right _
    apply hu.hasProdUniformlyOn_one_add hcompact
    · exact Filter.Eventually.of_forall fun i z hz => by
        dsimp [u]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hr i), norm_pow]
        exact mul_le_mul_of_nonneg_left (hmax z hz) (hr i)
    · intro i
      fun_prop


end
end StatMech.FrontierA
