/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc70butterflymeasure.Part2
import Def.StatisticalMechanics.Code.Walls.rc71disjpreserving
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc71_resolveMember_not_both (i : Fin n) (U : Finset (Fin n ⊕ Fin n)) :
    ¬ (Sum.inl i ∈ rc71_resolveMember i U ∧ Sum.inr i ∈ rc71_resolveMember i U) := by
  unfold rc71_resolveMember
  split_ifs with h
  · rintro ⟨_, hr⟩
    exact (Finset.notMem_erase _ _) hr
  · rintro ⟨hl, hr⟩
    exact h ⟨hl, hr⟩


theorem rc71_resolveLeft_disjPreserving_at (i : Fin n) (Fam : Finset (Finset (Fin n ⊕ Fin n))) :
    ∀ V ∈ rc71_resolveLeft i Fam, ¬ (Sum.inl i ∈ V ∧ Sum.inr i ∈ V) := by
  intro V hV
  rw [rc71_resolveLeft, Finset.mem_image] at hV
  obtain ⟨U, _, rfl⟩ := hV
  exact rc71_resolveMember_not_both i U


set_option maxRecDepth 4000 in


theorem rc71_witness_disjPreserving :
    rc70_DisjPreserving 2
      (rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})) := by
  decide

set_option maxRecDepth 4000 in


theorem rc71_witness_card_preserved :
    (rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})).card
      = (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}).card := by
  decide


end StatMech.Walls
