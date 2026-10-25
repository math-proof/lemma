/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PolygonWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Onsager.PolygonWalk.Part2


namespace StatMech.Onsager.PolygonWalk

theorem cornerBalance_eq_count {n : ℕ} (t : Fin n → ℤ)
    (h : ∀ i, t i = -1 ∨ t i = 0 ∨ t i = 1) [DecidablePred fun i => t i = 1]
    [DecidablePred fun i => t i = -1] :
    cornerBalance t
      = ((Finset.univ.filter fun i => t i = 1).card : ℤ)
        - ((Finset.univ.filter fun i => t i = -1).card : ℤ) := by
  classical
  unfold cornerBalance
  
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => t i = 1)]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun i => ¬ t i = 1)
        (fun i => t i = -1)]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i => t i = 1), t i
      = ((Finset.univ.filter fun i => t i = 1).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    simp
  have h2 : ∑ i ∈ (Finset.univ.filter (fun i => ¬ t i = 1)).filter (fun i => t i = -1), t i
      = - ((Finset.univ.filter fun i => t i = -1).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    have : (Finset.univ.filter (fun i => ¬ t i = 1)).filter (fun i => t i = -1)
        = Finset.univ.filter (fun i => t i = -1) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun ⟨_, h⟩ => h
      · intro h; exact ⟨by omega, h⟩
    rw [this]; simp
  have h3 : ∑ i ∈ (Finset.univ.filter (fun i => ¬ t i = 1)).filter (fun i => ¬ t i = -1), t i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_filter, Finset.mem_filter] at hi
    rcases h i with h' | h' | h' <;> simp_all
  rw [h1, h2, h3]; ring


end StatMech.Onsager.PolygonWalk
