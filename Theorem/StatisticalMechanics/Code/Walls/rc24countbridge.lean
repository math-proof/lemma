/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc23boxmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] in


theorem rc24_traceCond_antitone {K₁ K₂ S T : Finset α} (h : K₁ ⊆ K₂)
    (hT : T ∩ K₂ = S ∩ K₂) : T ∩ K₁ = S ∩ K₁ := by
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hxT, hxK₁⟩
    have hx2 : x ∈ T ∩ K₂ := Finset.mem_inter.mpr ⟨hxT, h hxK₁⟩
    rw [hT] at hx2
    exact ⟨(Finset.mem_inter.mp hx2).1, hxK₁⟩
  · rintro ⟨hxS, hxK₁⟩
    have hx2 : x ∈ S ∩ K₂ := Finset.mem_inter.mpr ⟨hxS, h hxK₁⟩
    rw [← hT] at hx2
    exact ⟨(Finset.mem_inter.mp hx2).1, hxK₁⟩


end StatMech.Walls
