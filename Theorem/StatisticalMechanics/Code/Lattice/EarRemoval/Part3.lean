/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Def.StatisticalMechanics.Code.Lattice.EarRemoval.Part3
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem domino_eq_insert : domino = insert (![0, 0] : Site 2) {![1, 0]} := rfl

theorem domino_finite : domino.Finite := by
  rw [domino_eq_insert]; exact (Set.finite_singleton _).insert _

theorem mem_domino_iff (v : Site 2) :
    v ∈ domino ↔ v = ![0, 0] ∨ v = ![1, 0] := by
  rw [domino_eq_insert, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem origin_mem_domino : (![0, 0] : Site 2) ∈ domino := by rw [mem_domino_iff]; exact Or.inl rfl

theorem one_mem_domino : (![1, 0] : Site 2) ∈ domino := by rw [mem_domino_iff]; exact Or.inr rfl


theorem mem_domino_coord_iff (v : Site 2) :
    v ∈ domino ↔ (v 0 = 0 ∧ v 1 = 0) ∨ (v 0 = 1 ∧ v 1 = 0) := by
  rw [mem_domino_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨by rw [h]; simp, by rw [h]; simp⟩
    · exact Or.inr ⟨by rw [h]; simp, by rw [h]; simp⟩
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · left; funext i; fin_cases i <;> simpa
    · right; funext i; fin_cases i <;> simpa


theorem not_mem_domino (v : Site 2)
    (h : ¬ ((v 0 = 0 ∧ v 1 = 0) ∨ (v 0 = 1 ∧ v 1 = 0))) : v ∉ domino := by
  rw [mem_domino_coord_iff]; exact h


end Lattice
end StatMech
