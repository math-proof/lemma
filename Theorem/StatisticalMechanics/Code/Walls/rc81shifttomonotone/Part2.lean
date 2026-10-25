/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc80structuredwall.Part3
import Def.StatisticalMechanics.Code.Walls.rc81shifttomonotone.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


variable {ι : Type*} [Fintype ι] [DecidableEq ι]


@[simp] theorem rc81_mem_upClosure {A : Finset (ConfigSpace ι)} (w : ConfigSpace ι) :
    w ∈ rc81_upClosure A ↔ ∃ a ∈ A, rc81_le a w = true := by simp [rc81_upClosure]

@[simp] theorem rc81_mem_downClosure {B : Finset (ConfigSpace ι)} (w : ConfigSpace ι) :
    w ∈ rc81_downClosure B ↔ ∃ b ∈ B, rc81_le w b = true := by simp [rc81_downClosure]


theorem rc81_subset_upClosure (A : Finset (ConfigSpace ι)) : A ⊆ rc81_upClosure A := by
  intro a ha; rw [rc81_mem_upClosure]; exact ⟨a, ha, (rc81_le_iff a a).mpr (fun i h => h)⟩


theorem rc81_subset_downClosure (B : Finset (ConfigSpace ι)) : B ⊆ rc81_downClosure B := by
  intro b hb; rw [rc81_mem_downClosure]; exact ⟨b, hb, (rc81_le_iff b b).mpr (fun i h => h)⟩


theorem rc81_upClosure_isUpper (A : Finset (ConfigSpace ι)) :
    rc80_IsUpper (rc81_upClosure A) := by
  intro a ha i
  rw [rc81_mem_upClosure] at ha ⊢
  obtain ⟨x, hx, hxa⟩ := ha
  rw [rc81_le_iff] at hxa
  refine ⟨x, hx, (rc81_le_iff _ _).mpr ?_⟩
  intro j hj
  by_cases hij : j = i
  · subst hij; simp [Function.update_self]
  · rw [Function.update_of_ne hij]; exact hxa j hj


theorem rc81_downClosure_isLower (B : Finset (ConfigSpace ι)) :
    rc80_IsLower (rc81_downClosure B) := by
  intro b hb i
  rw [rc81_mem_downClosure] at hb ⊢
  obtain ⟨x, hx, hbx⟩ := hb
  rw [rc81_le_iff] at hbx
  refine ⟨x, hx, (rc81_le_iff _ _).mpr ?_⟩
  intro j hj
  by_cases hij : j = i
  · subst hij; simp only [Function.update_self] at hj; exact absurd hj (by simp)
  · rw [Function.update_of_ne hij] at hj; exact hbx j hj


omit [DecidableEq ι] in

theorem rc81_reflInter_mono_left {A A' B : Finset (ConfigSpace ι)} (h : A ⊆ A') :
    rc80_reflInterG A B ⊆ rc80_reflInterG A' B := by
  intro a ha
  rw [rc80_reflInterG, Finset.mem_filter] at ha ⊢
  exact ⟨h ha.1, ha.2⟩


theorem rc81_upClosure_reflInter_ge (A B : Finset (ConfigSpace ι)) :
    (rc80_reflInterG A B).card ≤ (rc80_reflInterG (rc81_upClosure A) B).card :=
  Finset.card_le_card (rc81_reflInter_mono_left (rc81_subset_upClosure A))


end StatMech.Walls
