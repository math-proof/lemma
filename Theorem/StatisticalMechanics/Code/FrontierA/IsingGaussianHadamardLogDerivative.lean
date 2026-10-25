/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedHadamardPrereq
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanRootControl.Part2
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

theorem multipliableLocallyUniformlyOn_hadamardRootFactor
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) :
    MultipliableLocallyUniformlyOn (hadamardRootFactor roots) Set.univ := by
  unfold hadamardRootFactor
  refine ⟨fun z => ∏' n, (1 + (roots n : Complex) * z ^ 2), ?_⟩
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _hK hcompact
  rcases K.eq_empty_or_nonempty with rfl | hnonempty
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using
      tendstoUniformlyOn_empty
  · obtain ⟨z₀, hz₀, _hmaxEq, hmax⟩ :=
      hcompact.exists_sSup_image_eq_and_ge hnonempty
        (show ContinuousOn (fun z : Complex => ‖z‖ ^ 2) K by fun_prop)
    let u : Nat → Real := fun n => roots n * ‖z₀‖ ^ 2
    have hu : Summable u := hsum.mul_right _
    exact hu.hasProdUniformlyOn_nat_one_add hcompact
      (.of_forall fun n z hz => by
        dsimp [u]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hroots n), norm_pow]
        exact mul_le_mul_of_nonneg_left (hmax z hz) (hroots n))
      (fun _ => by fun_prop)


end
end StatMech.FrontierA
