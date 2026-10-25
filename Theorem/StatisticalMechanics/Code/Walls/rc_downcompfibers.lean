/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
open Finset
open scoped NNReal FinsetFamily


namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [Fintype E] in


theorem memberFiber_to_inter (i : E) (𝒜 : Finset (Finset E)) {s : Finset E} (hi : i ∉ s) :
    insert i s ∈ Down.compression i 𝒜 ↔ (insert i s ∈ 𝒜) ∧ (s ∈ 𝒜) := by
  rw [Down.mem_compression, Finset.erase_insert hi, Finset.insert_idem]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, h2⟩
    · exact absurd h2 h1
  · rintro ⟨h1, h2⟩
    exact Or.inl ⟨h1, h2⟩

omit [Fintype E] in


theorem nonMemberFiber_to_union (i : E) (𝒜 : Finset (Finset E)) {s : Finset E} (hi : i ∉ s) :
    s ∈ Down.compression i 𝒜 ↔ (insert i s ∈ 𝒜) ∨ (s ∈ 𝒜) := by
  rw [Down.mem_compression, Finset.erase_eq_of_notMem hi]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact Or.inr h1
    · exact Or.inl h2
  · rintro (h | h)
    · by_cases hs : s ∈ 𝒜
      · exact Or.inl ⟨hs, hs⟩
      · exact Or.inr ⟨hs, h⟩
    · exact Or.inl ⟨h, h⟩


end StatMech.Walls
