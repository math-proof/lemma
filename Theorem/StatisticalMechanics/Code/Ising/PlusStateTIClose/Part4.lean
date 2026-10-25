/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTI.Part2
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexUncond
import Def.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part4
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


theorem pstc_cylinderAlg_separatesPoints (d : ℕ) :
    (pstc_cylinderAlg d).SeparatesPoints := by
  rintro ω₁ ω₂ hne
  obtain ⟨x, hx⟩ : ∃ x, ω₁ x ≠ ω₂ x := by
    by_contra hc
    exact hne (funext fun x => not_not.mp (fun h => hc ⟨x, h⟩))
  refine ⟨(pstc_coordCM x : ConfigSpace (Site d) → ℝ),
    ⟨pstc_coordCM x, Algebra.subset_adjoin ⟨x, rfl⟩, rfl⟩, ?_⟩
  simp only [pstc_coordCM_apply]
  intro hcontra
  apply hx
  by_cases h1 : ω₁ x <;> by_cases h2 : ω₂ x <;> simp_all


end Ising
end StatMech
