/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc18nonmono.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Def.StatisticalMechanics.Code.Walls.rc19doublecover
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc19_cylBoxSupp_iff_doubled (A B : Set (ConfigSpace α)) (S : Finset α) :
    S ∈ rc18_cylBoxSupp A B ↔ (rc19_cylDoubledBox A B S).Nonempty := by
  rw [rc18_cylBoxSupp, Finset.mem_filter]
  constructor
  · rintro ⟨_, K, L, hKL, hKA, hLB⟩
    exact ⟨dbl K L, by
      rw [rc19_cylDoubledBox, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, K, L, rfl, hKL, hKA, hLB⟩⟩
  · rintro ⟨U, hU⟩
    rw [rc19_cylDoubledBox, Finset.mem_filter] at hU
    obtain ⟨_, K, L, _, hKL, hKA, hLB⟩ := hU
    exact ⟨Finset.mem_univ _, K, L, hKL, hKA, hLB⟩

omit [Fintype α] in


theorem rc19_dbl_inj {K L K' L' : Finset α} (h : dbl K L = dbl K' L') : K = K' ∧ L = L' := by
  have : (K, L) = (K', L') := dbl_injective (by simpa using h)
  rw [Prod.mk.injEq] at this
  exact this


theorem rc19_mem_reflInter_iff (A B : Set (ConfigSpace α)) (S : Finset α) :
    S ∈ rc10_reflInter (eventFamily A) (eventFamily B) ↔
      supportCfg S ∈ A ∧ supportCfg (Sᶜ) ∈ B := by
  classical
  rw [rc10_reflInter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨?_, ?_⟩
    · rw [rc10_mem_iff_eventFamily A, cfgSupport_supportCfg]; exact hA
    · rw [rc10_mem_iff_eventFamily B, cfgSupport_supportCfg]; exact hB
  · rintro ⟨hA, hB⟩
    refine ⟨?_, ?_⟩
    · rw [rc10_mem_iff_eventFamily A (supportCfg S), cfgSupport_supportCfg] at hA; exact hA
    · rw [rc10_mem_iff_eventFamily B (supportCfg Sᶜ), cfgSupport_supportCfg] at hB; exact hB

open Classical in


theorem rc19_reflInter_diag_injOn (A B : Set (ConfigSpace α)) :
    Set.InjOn (fun S : Finset α => dbl S Sᶜ)
      (rc10_reflInter (eventFamily A) (eventFamily B) : Set (Finset α)) := by
  intro S _ S' _ h
  simp only at h
  exact (rc19_dbl_inj h).1


end StatMech.Walls
