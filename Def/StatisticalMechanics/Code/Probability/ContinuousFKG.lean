/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Probability.ContinuousFKG
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech

namespace Probability

set_option linter.unusedSectionVars false


def HasFKG {β : Type*} [MeasurableSpace β] [Preorder β] (ν : Measure β) : Prop :=
  ∀ (f g : β → ℝ), Measurable f → Measurable g →
    (∃ Cf : ℝ, ∀ b, |f b| ≤ Cf) → (∃ Cg : ℝ, ∀ b, |g b| ≤ Cg) →
    Monotone f → Monotone g →
    (∫ b, f b ∂ν) * (∫ b, g b ∂ν) ≤ ∫ b, f b * g b ∂ν


end Probability
end StatMech
