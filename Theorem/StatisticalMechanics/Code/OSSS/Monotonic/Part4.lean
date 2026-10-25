/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Def.StatisticalMechanics.Code.OSSS.Monotonic.Part4
open Finset


namespace StatMech

namespace OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem fkg_implies_monotonic {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hFKG : FKGLatticeCondition μ) : IsMonotonicMeasure μ := by
  intro e F ξ ζ hle hZξ hZζ
  have hμ : 0 ≤ μ := fun ω => (hpos ω).le
  
  have hdom := holley_dominates
    (μ₁ := condMass μ F ξ) (μ₂ := condMass μ F ζ)
    (condMass_nonneg hμ F ξ hZξ) (condMass_nonneg hμ F ζ hZζ)
    (by rw [condMass_sum F ξ hZξ.ne', condMass_sum F ζ hZζ.ne'])
    (cross_condMass hμ hFKG F ξ ζ hle hZξ hZζ)
    (isIncreasing_openAt e)
  exact hdom

end OSSS.Monotonic
end StatMech
