/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.FK.InclusionExclusion
open StatMech ConfigSpace
open scoped BigOperators Pointwise


namespace StatMech

namespace FK

variable {E : Type*}


lemma one_mem_incrIndicators : (1 : ConfigSpace E → ℝ) ∈ incrIndicators E :=
  ⟨Set.univ, isUpperSet_univ, by simp⟩


lemma openEvent_increasing (e : E) : IsIncreasing {ω : ConfigSpace E | ω e = true} := by
  intro x y hxy hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  exact Bool.le_iff_imp.mp (hxy e) hx


lemma openIndicator_mem (e : E) :
    ({ω : ConfigSpace E | ω e = true}).indicator (1 : ConfigSpace E → ℝ) ∈ incrIndicators E :=
  ⟨_, openEvent_increasing e, rfl⟩


end FK
end StatMech
