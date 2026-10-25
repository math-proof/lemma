/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc11bkriffincinc
import Theorem.StatisticalMechanics.Code.Walls.rc11boxsuppupper
import Theorem.StatisticalMechanics.Code.Walls.rc11reflinterstructure
import Theorem.StatisticalMechanics.Code.Walls.rc11doublecoverrepresentation
import Theorem.StatisticalMechanics.Code.Walls.rc11compressionengine
import Def.StatisticalMechanics.Code.Walls.rc11core.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc11_bkr_of_injectionAll (h : rc11_BKRInjectionAll) : rc10_BKRSetFamily :=
  fun n 𝒜 ℬ h𝒜 hℬ => rc11_card_le_of_injection (h n 𝒜 ℬ h𝒜 hℬ)


theorem rc11_injectionAll_of_bkr (h : rc10_BKRSetFamily) : rc11_BKRInjectionAll :=
  fun n 𝒜 ℬ h𝒜 hℬ => rc11_injection_of_card_le (h n 𝒜 ℬ h𝒜 hℬ)


theorem rc11_BKRInjectionAll_iff_bkr : rc11_BKRInjectionAll ↔ rc10_BKRSetFamily :=
  ⟨rc11_bkr_of_injectionAll, rc11_injectionAll_of_bkr⟩


open Classical in


theorem rc11_boxSupp_not_downComp_mono :
    ∃ 𝒜 : Finset (Finset (Fin 2)),
      #(rc10_boxSupp 𝒜 𝒜) < #(rc10_boxSupp (Down.compression 0 𝒜) (Down.compression 0 𝒜)) := by
  refine ⟨{{0}, {0, 1}}, ?_⟩
  decide

open Classical in


theorem rc11_bkr_false_lower :
    ∃ 𝒜 : Finset (Finset (Fin 2)),
      IsLowerSet (𝒜 : Set (Finset (Fin 2))) ∧
        #(rc10_reflInter 𝒜 𝒜) < #(rc10_boxSupp 𝒜 𝒜) := by
  refine ⟨{∅, {0}}, ?_, ?_⟩
  · intro S T hTS hS
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hS ⊢
    rcases hS with rfl | rfl
    · left; exact Finset.subset_empty.mp hTS
    · 
      have : T ⊆ ({0} : Finset (Fin 2)) := hTS
      rcases Finset.subset_singleton_iff.mp this with rfl | rfl
      · left; rfl
      · right; rfl
  · decide


open Classical in


theorem rc11_core_doubleCover (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc10_boxSupp 𝒜 ℬ ↔ ∃ U ∈ boxDoubled 𝒜 ℬ, U.image (Sum.elim id id) ⊆ S :=
  rc11_boxSupp_iff_collapse 𝒜 ℬ S


theorem rc11_core_compressionEngine {β : Type*} [DecidableEq β] (𝒜 ℬ : Finset (Finset β)) :
    ((boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ)
      ∧ (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ))
      ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ)
            - dpairsCount 𝒜 ℬ
          = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
            - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
                (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i))
      ∧ (∀ cs : List β, (iterDownComp cs 𝒜).card = 𝒜.card)
      ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β))
            ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ))
      ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β,
            dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
              ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) :=
  rc11_compressionEngine 𝒜 ℬ


open Classical in


theorem rc11_injection_fin0 (𝒜 ℬ : Finset (Finset (Fin 0)))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin 0)))) (hℬ : IsUpperSet (ℬ : Set (Finset (Fin 0)))) :
    rc11_BKRInjection 𝒜 ℬ :=
  rc11_injection_of_card_le (rc11_bkr_fin0 𝒜 ℬ h𝒜 hℬ)

open Classical in


theorem rc11_injection_fin1 (𝒜 ℬ : Finset (Finset (Fin 1)))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin 1)))) (hℬ : IsUpperSet (ℬ : Set (Finset (Fin 1)))) :
    rc11_BKRInjection 𝒜 ℬ :=
  rc11_injection_of_card_le (rc11_bkr_fin1 𝒜 ℬ h𝒜 hℬ)


theorem rc11_core_bkr_setfamily :
    (rc11_BKRInjectionAll ↔ rc10_BKRSetFamily)
      ∧ (rc10_BKRSetFamily ↔ rc10_DeficitBridgeIncInc)
      ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 0)), IsUpperSet (𝒜 : Set (Finset (Fin 0))) →
          IsUpperSet (ℬ : Set (Finset (Fin 0))) →
            #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 1)), IsUpperSet (𝒜 : Set (Finset (Fin 1))) →
          IsUpperSet (ℬ : Set (Finset (Fin 1))) →
            #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (∃ 𝒜 : Finset (Finset (Fin 2)),
          #(rc10_boxSupp 𝒜 𝒜) < #(rc10_boxSupp (Down.compression 0 𝒜) (Down.compression 0 𝒜))) :=
  ⟨rc11_BKRInjectionAll_iff_bkr,
    rc11_bkr_iff_deficitIncInc,
    rc11_bkr_fin0,
    rc11_bkr_fin1,
    rc11_boxSupp_not_downComp_mono⟩

end StatMech.Walls
