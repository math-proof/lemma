/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.FK.IndexedBoundaryCondition
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FK

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]


theorem indexedOpenGraph_inf_le
    (ends : E -> Sym2 V) (a b : E -> Bool) :
    indexedOpenGraph ends (a ⊓ b) <=
      indexedOpenGraph ends a ⊓ indexedOpenGraph ends b := by
  intro x y hxy
  rw [SimpleGraph.inf_adj]
  simp only [indexedOpenGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_setOf_eq] at hxy ⊢
  obtain ⟨⟨i, hi, hab⟩, hne⟩ := hxy
  have hab' : a i = true ∧ b i = true := by simpa using hab
  have ha : a i = true := hab'.1
  have hb : b i = true := hab'.2
  exact ⟨⟨⟨i, hi, ha⟩, hne⟩, ⟨⟨i, hi, hb⟩, hne⟩⟩

theorem indexedOpenGraph_sup
    (ends : E -> Sym2 V) (a b : E -> Bool) :
    indexedOpenGraph ends (a ⊔ b) =
      indexedOpenGraph ends a ⊔ indexedOpenGraph ends b := by
  ext x y
  simp only [indexedOpenGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_setOf_eq, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨⟨i, hi, hab⟩, hne⟩
    have hor : a i = true ∨ b i = true := by
      simpa using hab
    rcases hor with ha | hb
    · exact Or.inl ⟨⟨i, hi, ha⟩, hne⟩
    · exact Or.inr ⟨⟨i, hi, hb⟩, hne⟩
  · rintro (⟨⟨i, hi, ha⟩, hne⟩ | ⟨⟨i, hi, hb⟩, hne⟩)
    · exact ⟨⟨i, hi, by simp [ha]⟩, hne⟩
    · exact ⟨⟨i, hi, by simp [hb]⟩, hne⟩


end
end StatMech.FK
