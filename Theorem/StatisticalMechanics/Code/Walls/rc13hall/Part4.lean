/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc12reimerinjection.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc10core.Part4
import Def.StatisticalMechanics.Code.Walls.rc13hall.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc13_marriageSearch_iff_marriage (𝒜 ℬ : Finset (Finset (Fin 2))) :
    rc13_marriageSearch 𝒜 ℬ = true ↔ rc13_MarriageCondition 𝒜 ℬ := by
  have hfun : rc13_admComp 𝒜 ℬ = rc13_adm 𝒜 ℬ := funext (rc13_admComp_eq 𝒜 ℬ)
  rw [rc13_marriageSearch, decide_eq_true_eq, rc13_MarriageCondition]
  constructor
  · intro h 𝒯 h𝒯
    have h𝒯' : 𝒯 ∈ (rc12_boxSuppComp 𝒜 ℬ).powerset := by
      rw [Finset.mem_powerset, rc12_boxSuppComp_eq]; exact h𝒯
    have := h 𝒯 h𝒯'
    rwa [hfun] at this
  · intro h 𝒯 h𝒯
    rw [Finset.mem_powerset, rc12_boxSuppComp_eq] at h𝒯
    have := h 𝒯 h𝒯
    rwa [hfun]


set_option maxHeartbeats 8000000 in


theorem rc13_marriageSearch_iff_card_fin2 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc12_isUpperFin 2 𝒜 → rc12_isUpperFin 2 ℬ →
      (rc13_marriageSearch 𝒜 ℬ = true ↔
        (rc12_boxSuppComp 𝒜 ℬ).card ≤ (rc12_reflInterComp 𝒜 ℬ).card) := by
  decide

set_option maxHeartbeats 4000000 in


theorem rc13_marriageSearch_fin2_holds :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc12_isUpperFin 2 𝒜 → rc12_isUpperFin 2 ℬ →
      rc13_marriageSearch 𝒜 ℬ = true := by
  decide


theorem rc13_hall_route_is_circular :
    (∀ 𝒜 ℬ : Finset (Finset α),
        rc13_MarriageCondition 𝒜 ℬ ↔ rc12_ReimerReflectionInjection 𝒜 ℬ)
      ∧ (∀ 𝒜 ℬ : Finset (Finset α),
          rc13_MarriageCondition 𝒜 ℬ ↔
            ∃ g : rc10_boxSupp 𝒜 ℬ → Finset α,
              Function.Injective g ∧ ∀ x, g x ∈ rc13_adm 𝒜 ℬ x.val)
      ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc12_isUpperFin 2 𝒜 → rc12_isUpperFin 2 ℬ →
          (rc13_marriageSearch 𝒜 ℬ = true ↔
            (rc12_boxSuppComp 𝒜 ℬ).card ≤ (rc12_reflInterComp 𝒜 ℬ).card)) :=
  ⟨rc13_marriage_iff_reflectionInjection,
    rc13_marriage_iff_transversal,
    rc13_marriageSearch_iff_card_fin2⟩

end StatMech.Walls
