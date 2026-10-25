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
import Def.StatisticalMechanics.Code.Walls.rc58bipartiteflow.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc58_kadmSDR_closes_wall (h : rc58_KadmSDR) : rc20_FamCylBoxResidue := by
  intro n 𝒜 ℬ
  obtain ⟨f, hinj, hmem⟩ := h n 𝒜 ℬ
  refine Finset.card_le_card_of_injOn f (fun S hS => ?_) hinj
  exact rc58_kadm_subset_reflInter n 𝒜 ℬ S (hmem S hS)

open Classical in


theorem rc58_reimer_closes_of_kadmSDR (h : rc58_KadmSDR) : rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue (rc58_kadmSDR_closes_wall h)

open Classical in


theorem rc58_kadm_hall_iff_sdr (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    (∀ 𝒮 : Finset (rc20_famCylBox 𝒜 ℬ),
        #𝒮 ≤ #(𝒮.biUnion (fun S => rc58_kadm n 𝒜 ℬ (S : Finset (Fin n))))) ↔
      ∃ f : (rc20_famCylBox 𝒜 ℬ) → Finset (Fin n),
        Function.Injective f ∧
          ∀ S : (rc20_famCylBox 𝒜 ℬ), f S ∈ rc58_kadm n 𝒜 ℬ (S : Finset (Fin n)) :=
  Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun S : (rc20_famCylBox 𝒜 ℬ) => rc58_kadm n 𝒜 ℬ (S : Finset (Fin n)))


end StatMech.Walls
