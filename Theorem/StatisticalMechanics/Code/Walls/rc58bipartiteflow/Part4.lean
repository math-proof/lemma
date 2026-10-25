/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc57witnessed.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc58bipartiteflow.Part4
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


set_option maxRecDepth 4000 in


theorem rc58_kadm_hall_holds_on_rc57pair :
    ∀ 𝒯 ∈ (rc20_famCylBoxComp 2 rc58_Arc57 rc58_Brc57).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc58_kadm 2 rc58_Arc57 rc58_Brc57)).card := by
  rw [rc58_Arc57, rc58_Brc57]; decide

set_option maxRecDepth 4000 in


theorem rc58_kadm_proper_on_rc57pair :
    (rc58_kadm 2 rc58_Arc57 rc58_Brc57 {0}).card
      < (rc20_reflInterComp 2 rc58_Arc57 rc58_Brc57).card := by
  rw [rc58_Arc57, rc58_Brc57]; decide


open Classical in


theorem rc58_reimer_bipartiteFlow :
    (¬ rc22_BoxCompressionMono)
      ∧ ((rc20_famCylBoxComp 2 rc58_Amono rc58_Bmono).card
          ≤ (rc20_reflInterComp 2 rc58_Amono rc58_Bmono).card)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))),
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔
            Nonempty ((rc20_famCylBox 𝒜 ℬ : Finset (Finset (Fin 2)))
              ↪ (rc10_reflInter 𝒜 ℬ : Finset (Finset (Fin 2)))))
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)),
          rc58_kadm n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ)
      ∧ (rc58_KadmSDR → rc18_CylBoxReflInter)
      ∧ (∀ 𝒯 ∈ (rc20_famCylBoxComp 2 rc58_Arc57 rc58_Brc57).powerset,
          𝒯.card ≤ (𝒯.biUnion (rc58_kadm 2 rc58_Arc57 rc58_Brc57)).card)
      ∧ ((rc58_kadm 2 rc58_Arc57 rc58_Brc57 {0}).card
          < (rc20_reflInterComp 2 rc58_Arc57 rc58_Brc57).card) :=
  ⟨rc58_boxCompressionMono_false,
    rc58_wall_holds_on_monoCE,
    fun 𝒜 ℬ => rc58_matching_iff_wall 𝒜 ℬ,
    rc58_kadm_subset_reflInter,
    rc58_reimer_closes_of_kadmSDR,
    rc58_kadm_hall_holds_on_rc57pair,
    rc58_kadm_proper_on_rc57pair⟩

end StatMech.Walls
