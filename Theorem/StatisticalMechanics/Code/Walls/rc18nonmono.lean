/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc17arbitrary.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc10core.Part4
import Theorem.StatisticalMechanics.Code.Walls.rmr_cylinderwitness
import Def.StatisticalMechanics.Code.Walls.rc18nonmono
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc18_card_box_eq_cylBoxSupp (A B : Set (ConfigSpace α)) :
    #(univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B))
      = #(rc18_cylBoxSupp A B) := by
  classical
  apply Finset.card_bij (fun ω _ => cfgSupport ω)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    rw [mem_disjointOccurrence_iff_cylinder] at hω
    obtain ⟨K, L, hKL, hKA, hLB⟩ := hω
    rw [rc18_cylBoxSupp, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, K, L, hKL, ?_, ?_⟩
    · rwa [supportCfg_cfgSupport]
    · rwa [supportCfg_cfgSupport]
  · intro a _ b _ hab
    have := congrArg supportCfg hab
    rwa [supportCfg_cfgSupport, supportCfg_cfgSupport] at this
  · intro S hS
    rw [rc18_cylBoxSupp, Finset.mem_filter] at hS
    obtain ⟨_, K, L, hKL, hKA, hLB⟩ := hS
    refine ⟨supportCfg S, ?_, cfgSupport_supportCfg S⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_disjointOccurrence_iff_cylinder]
    exact ⟨K, L, hKL, hKA, hLB⟩


end StatMech.Walls
