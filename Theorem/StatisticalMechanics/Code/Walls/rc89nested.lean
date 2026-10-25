/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc88twogen.Part2
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc89_occ_self_mem (X : Finset (ConfigSpace ι)) (S : Finset ι) (w : ConfigSpace ι)
    (h : rc80_occ X S w = true) : w ∈ X := by
  unfold rc80_occ at h
  rw [decide_eq_true_eq] at h
  exact h w (fun _ _ => rfl)


theorem rc89_disjOccG_subset_inter (A B : Finset (ConfigSpace ι)) :
    rc80_disjOccG A B ⊆ A ∩ B := by
  intro w hw
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  obtain ⟨K, L, _, hK, hL⟩ := hw
  exact Finset.mem_inter.mpr ⟨rc89_occ_self_mem A K w hK, rc89_occ_self_mem B L w hL⟩


theorem rc89_disjOccG_eq_empty_of_disjoint (A B : Finset (ConfigSpace ι))
    (h : A ∩ B = ∅) : rc80_disjOccG A B = ∅ := by
  rw [← Finset.subset_empty, ← h]
  exact rc89_disjOccG_subset_inter A B


theorem rc89_wall_disjoint (A B : Finset (ConfigSpace ι)) (h : A ∩ B = ∅) :
    (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card := by
  rw [rc89_disjOccG_eq_empty_of_disjoint A B h, Finset.card_empty]
  exact Nat.zero_le _


end StatMech.Walls
