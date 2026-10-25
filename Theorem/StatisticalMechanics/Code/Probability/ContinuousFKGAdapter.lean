/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKGAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.ContinuousFKG.Part3
import Instance.StatisticalMechanics.Code.Probability.ContinuousFKGAdapter
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech

namespace Probability

set_option linter.unusedSectionVars false


theorem cube_eq (n : ℕ) :
    cube n = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rfl


theorem fkg_of_factor {α : Type*} [MeasurableSpace α] [Preorder α] (n : ℕ)
    (p : (Fin n → ℝ) → α) (hpm : Measurable p) (hpmono : Monotone p)
    {f₀ g₀ : α → ℝ} (hf₀m : Measurable f₀) (hg₀m : Measurable g₀)
    {Cf Cg : ℝ} (hf₀C : ∀ a, |f₀ a| ≤ Cf) (hg₀C : ∀ a, |g₀ a| ≤ Cg)
    (hf₀ : Monotone f₀) (hg₀ : Monotone g₀) :
    (∫ x, f₀ (p x) ∂(cube n)) * (∫ x, g₀ (p x) ∂(cube n))
      ≤ ∫ x, f₀ (p x) * g₀ (p x) ∂(cube n) := by
  rw [cube_eq]
  exact continuous_fkg n (hf₀m.comp hpm) (hg₀m.comp hpm)
    (fun x => hf₀C _) (fun x => hg₀C _) (hf₀.comp hpmono) (hg₀.comp hpmono)


end Probability
end StatMech
