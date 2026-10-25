/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc19doublecover.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc20_mem_eventFamily_iff (A : Set (ConfigSpace α)) (S : Finset α) :
    S ∈ eventFamily A ↔ supportCfg S ∈ A := by
  rw [rc10_mem_iff_eventFamily A (supportCfg S), cfgSupport_supportCfg]

open Classical in


theorem rc20_eventFamily_univ : eventFamily (Set.univ : Set (ConfigSpace α)) = univ := by
  ext S
  simp only [rc20_mem_eventFamily_iff, Set.mem_univ, Finset.mem_univ]


omit [Fintype α] in


theorem rc20_agree_iff_inter (K S T : Finset α) :
    (∀ e ∈ K, supportCfg T e = supportCfg S e) ↔ T ∩ K = S ∩ K := by
  constructor
  · intro h
    ext e
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨heT, heK⟩
      have := h e heK
      simp only [supportCfg_apply, decide_eq_decide] at this
      exact ⟨this.mp heT, heK⟩
    · rintro ⟨heS, heK⟩
      have := h e heK
      simp only [supportCfg_apply, decide_eq_decide] at this
      exact ⟨this.mpr heS, heK⟩
  · intro h e heK
    simp only [supportCfg_apply, decide_eq_decide]
    constructor
    · intro heT
      have : e ∈ T ∩ K := Finset.mem_inter.mpr ⟨heT, heK⟩
      rw [h] at this
      exact (Finset.mem_inter.mp this).1
    · intro heS
      have : e ∈ S ∩ K := Finset.mem_inter.mpr ⟨heS, heK⟩
      rw [← h] at this
      exact (Finset.mem_inter.mp this).1

open Classical in


theorem rc20_cylinder_subset_iff_family (A : Set (ConfigSpace α)) (K S : Finset α) :
    cylinder K (supportCfg S) ⊆ A ↔ ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ eventFamily A := by
  constructor
  · intro hcyl T hT
    rw [rc20_mem_eventFamily_iff]
    apply hcyl
    rw [mem_cylinder]
    exact (rc20_agree_iff_inter K S T).mpr hT
  · intro hfam ω' hω'
    rw [mem_cylinder] at hω'
    
    have hkey : cfgSupport ω' ∈ eventFamily A := by
      apply hfam
      apply (rc20_agree_iff_inter K S (cfgSupport ω')).mp
      intro e heK
      rw [supportCfg_cfgSupport]
      exact hω' e heK
    rw [rc20_mem_eventFamily_iff, supportCfg_cfgSupport] at hkey
    exact hkey


open Classical in


theorem rc20_cylBoxSupp_self_mem {A B : Set (ConfigSpace α)} {S : Finset α}
    (hS : S ∈ rc18_cylBoxSupp A B) : supportCfg S ∈ A ∧ supportCfg S ∈ B := by
  rw [rc18_cylBoxSupp, Finset.mem_filter] at hS
  obtain ⟨_, K, L, _, hKA, hLB⟩ := hS
  exact ⟨hKA (self_mem_cylinder K (supportCfg S)), hLB (self_mem_cylinder L (supportCfg S))⟩

open Classical in


theorem rc20_cylBoxSupp_mem_eventFamily {A B : Set (ConfigSpace α)} {S : Finset α}
    (hS : S ∈ rc18_cylBoxSupp A B) : S ∈ eventFamily A :=
  (rc20_mem_eventFamily_iff A S).mpr (rc20_cylBoxSupp_self_mem hS).1


end StatMech.Walls
