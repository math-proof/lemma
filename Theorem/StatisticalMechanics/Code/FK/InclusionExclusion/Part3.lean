/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.FK.InclusionExclusion.Part3
open StatMech ConfigSpace
open scoped BigOperators Pointwise


namespace StatMech

namespace FK

variable {E : Type*}


lemma cyl_indicator_eq_prod (S : Finset E) (ψ : ConfigSpace E) :
    (cyl S ψ).indicator (1 : ConfigSpace E → ℝ)
      = ∏ e ∈ S, (fun ω : ConfigSpace E => if ω e = ψ e then (1 : ℝ) else 0) := by
  classical
  ext ω
  rw [Finset.prod_apply, Set.indicator_apply]
  simp only [cyl, Set.mem_setOf_eq, Pi.one_apply]
  split_ifs with h
  · symm; exact Finset.prod_eq_one fun e he => if_pos (h e he)
  · symm
    obtain ⟨e, he, hne⟩ : ∃ e ∈ S, ω e ≠ ψ e := by
      by_contra hcon
      exact h fun e he => not_ne_iff.mp fun hne => hcon ⟨e, he, hne⟩
    exact Finset.prod_eq_zero he (if_neg hne)


theorem cyl_indicator_signedIncreasingCombo (S : Finset E) (ψ : ConfigSpace E) :
    SignedIncreasingCombo ((cyl S ψ).indicator (1 : ConfigSpace E → ℝ)) := by
  rw [SignedIncreasingCombo, cyl_indicator_eq_prod]
  exact prod_mem_span S _ fun e _ => matcher_mem e (ψ e)

end FK
end StatMech
