/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc9core.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part4
import Def.StatisticalMechanics.Code.Walls.rc10core
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc10_card_box_eq (A B : Set (ConfigSpace α)) (hA : IsIncreasing A) (hB : IsIncreasing B) :
    #(univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B))
      = #(rc10_boxSupp (eventFamily A) (eventFamily B)) := by
  classical
  rw [rc10_boxSupp]
  apply rc10_card_via_support
  intro ω
  rw [rc10_box_increasing_iff hA hB ω]
  constructor
  · rintro ⟨K, L, hKL, hKsub, hLsub, hKA, hLB⟩
    refine ⟨K, L, hKL, hKsub, hLsub, ?_, ?_⟩
    · simp only [eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨supportCfg K, hKA, cfgSupport_supportCfg K⟩
    · simp only [eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨supportCfg L, hLB, cfgSupport_supportCfg L⟩
  · rintro ⟨K, L, hKL, hKsub, hLsub, hKA, hLB⟩
    refine ⟨K, L, hKL, hKsub, hLsub, ?_, ?_⟩
    · simp only [eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hKA
      obtain ⟨ω', hω', hω'K⟩ := hKA
      rw [← hω'K, supportCfg_cfgSupport]; exact hω'
    · simp only [eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hLB
      obtain ⟨ω', hω', hω'L⟩ := hLB
      rw [← hω'L, supportCfg_cfgSupport]; exact hω'


theorem rc10_mem_iff_eventFamily (A : Set (ConfigSpace α)) (ω : ConfigSpace α) :
    ω ∈ A ↔ cfgSupport ω ∈ eventFamily A := by
  conv_lhs => rw [← rit_familyEvent_eventFamily A]
  rfl

open Classical in


theorem rc10_card_reflInter_eq (A B : Set (ConfigSpace α)) :
    #(univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B))
      = #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
  classical
  rw [rc10_reflInter]
  apply rc10_card_via_support
  intro ω
  simp only [Set.mem_inter_iff, rmr_mem_reflect]
  rw [rc10_mem_iff_eventFamily A ω, rc10_mem_iff_eventFamily B (rmr_compl ω),
    rc10_cfgSupport_compl]


end StatMech.Walls
