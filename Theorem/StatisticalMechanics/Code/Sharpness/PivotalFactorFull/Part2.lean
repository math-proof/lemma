/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Def.StatisticalMechanics.Code.Sharpness.PivotalFactorFull.Part2
open MeasureTheory Function Set
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem mem_internalEdgesFinset {S : Finset (Site d)} {e : Sym2 (Site d)} :
    e ∈ internalEdgesFinset S ↔ ∃ x ∈ S, ∃ y ∈ S, e = s(x, y) := by
  simp only [internalEdgesFinset, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, he⟩; exact ⟨x, hx, y, hy, he.symm⟩
  · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩


theorem internalEdgesFinset_coe (S : Finset (Site d)) :
    (internalEdgesFinset S : Set (Sym2 (Site d))) = internalEdges (S : Set _) := by
  ext e
  rw [Finset.mem_coe, mem_internalEdgesFinset]
  simp only [internalEdges, Set.mem_setOf_eq, Finset.mem_coe]


theorem shp_internalEdges_disjoint {S : Set (Site d)} {U : Set (Sym2 (Site d))}
    (hU : ∀ e ∈ U, ∃ a b : Site d, e = s(a, b) ∧ (a ∉ S ∨ b ∉ S)) :
    Disjoint (internalEdges S) U := by
  rw [Set.disjoint_left]
  rintro e ⟨x, hx, y, hy, rfl⟩ heU
  obtain ⟨a, b, hab, hout⟩ := hU _ heU
  rw [Sym2.eq_iff] at hab
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> subst ha <;> subst hb <;>
    rcases hout with h | h <;> exact h (by assumption)


theorem shp_internalEdgesFinset_disjoint {S : Finset (Site d)} {U : Finset (Sym2 (Site d))}
    (hU : ∀ e ∈ U, ∃ a b : Site d, e = s(a, b) ∧ (a ∉ S ∨ b ∉ S)) :
    Disjoint (internalEdgesFinset S) U := by
  rw [Finset.disjoint_left]
  intro e he heU
  rw [mem_internalEdgesFinset] at he
  obtain ⟨x, hx, y, hy, rfl⟩ := he
  obtain ⟨a, b, hab, hout⟩ := hU _ heU
  rw [Sym2.eq_iff] at hab
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> subst ha <;> subst hb <;>
    rcases hout with h | h <;> exact h (by assumption)


end Sharpness
end StatMech
