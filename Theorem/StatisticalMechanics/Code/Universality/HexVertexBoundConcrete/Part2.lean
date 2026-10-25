/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexBoundConcrete


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


theorem hexVBC_star_mem (m s : ℂ) (α β : ℝ)
    (hin : (α, β) = ((1 : ℝ), (0 : ℝ)) ∨ (α, β) = (1, 1) ∨ (α, β) = (0, 1) ∨
       (α, β) = (-1, 0) ∨ (α, β) = (-1, -1) ∨ (α, β) = (0, -1)) :
    m + ((α : ℂ) + (β : ℂ) * hexOmega) * s ∈ hexVBC_star m s := by
  unfold hexVBC_star
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hin with h | h | h | h | h | h <;>
    (rw [Prod.ext_iff] at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; push_cast; tauto)


end StatMech.Universality
