/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_sixVertexLocalDisagreementSides
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4) :
    d ∈ sixVertexLocalDisagreementSides p q ↔ p d ≠ q d := by
  simp [sixVertexLocalDisagreementSides]

theorem card_sixVertexLocalDisagreementSides
    (p q : SixVertexLocalIncomingPattern) :
    (sixVertexLocalDisagreementSides p q).card =
      ∑ d, if p d ≠ q d then 1 else 0 := by
  classical
  rw [Finset.card_eq_sum_ones, sixVertexLocalDisagreementSides,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : p d = q d <;> simp [h]


theorem existsUnique_mem_ne_of_card_eq_two
    {α : Type*} [DecidableEq α] (s : Finset α) (d : α)
    (hcard : s.card = 2) (hd : d ∈ s) :
    ∃! e, e ∈ s ∧ e ≠ d := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · refine ⟨b, by simp [hab.symm], ?_⟩
    intro e he
    rcases he with ⟨he, hne⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact False.elim (hne rfl)
    · rfl
  · refine ⟨a, by simp [hab], ?_⟩
    intro e he
    rcases he with ⟨he, hne⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · rfl
    · exact False.elim (hne rfl)


end
end StatMech.FrontierD
