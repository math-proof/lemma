/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc18nonmono.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc19_mem_cylBoxSupp_iff_minimal (A B : Set (ConfigSpace α)) (S : Finset α) :
    S ∈ rc18_cylBoxSupp A B ↔
      ∃ K L : Finset α, Disjoint K L ∧
        Minimal (fun T => cylinder T (supportCfg S) ⊆ A) K ∧
        Minimal (fun T => cylinder T (supportCfg S) ⊆ B) L := by
  rw [rc18_cylBoxSupp, Finset.mem_filter]
  constructor
  · rintro ⟨_, K, L, hKL, hKA, hLB⟩
    obtain ⟨K₀, hK0sub, hK0min⟩ := exists_minimal_cylinder_witness hKA
    obtain ⟨L₀, hL0sub, hL0min⟩ := exists_minimal_cylinder_witness hLB
    exact ⟨K₀, L₀,
      Finset.disjoint_of_subset_left hK0sub (Finset.disjoint_of_subset_right hL0sub hKL),
      hK0min, hL0min⟩
  · rintro ⟨K, L, hKL, hKmin, hLmin⟩
    exact ⟨Finset.mem_univ _, K, L, hKL, hKmin.1, hLmin.1⟩


end StatMech.Walls
