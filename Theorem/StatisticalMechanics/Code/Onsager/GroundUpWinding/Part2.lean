/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Onsager.GroundUpWinding


namespace StatMech.Onsager.GroundUp

theorem turnSum_eq {n : ℕ} (t : Fin n → ℤ) (h : ∀ i, t i = 1 ∨ t i = -1) :
    turnSum t = (convexCount t : ℤ) - reflexCount t := by
  classical
  unfold turnSum convexCount reflexCount
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => t i = 1) t]
  have hset : Finset.univ.filter (fun i => ¬ t i = 1)
      = Finset.univ.filter (fun i => t i = -1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases h i with h1 | h1 <;> rw [h1] <;> decide
  have e1 : ∑ i ∈ Finset.univ.filter (fun i => t i = 1), t i
      = ((Finset.univ.filter (fun i => t i = 1)).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.1 hi).2)]
    simp
  have e2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ t i = 1), t i
      = - ((Finset.univ.filter (fun i => t i = -1)).card : ℤ) := by
    rw [hset, Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.1 hi).2)]
    simp
  rw [e1, e2]; ring


theorem card_split {n : ℕ} (t : Fin n → ℤ) (h : ∀ i, t i = 1 ∨ t i = -1) :
    convexCount t + reflexCount t = n := by
  classical
  unfold convexCount reflexCount
  have hset : Finset.univ.filter (fun i => t i = -1)
      = Finset.univ.filter (fun i => ¬ t i = 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases h i with h1 | h1 <;> rw [h1] <;> decide
  rw [hset, Finset.card_filter_add_card_filter_not]
  simp


theorem balance_split (c r c₁ r₁ c₂ r₂ : ℤ)
    (hc : c₁ + c₂ = c + 3) (hr : r₁ + r₂ = r - 1) :
    (c - r) = (c₁ - r₁) + (c₂ - r₂) - 4 := by
  omega


theorem balance_of_split (c r c₁ r₁ c₂ r₂ : ℤ)
    (hc : c₁ + c₂ = c + 3) (hr : r₁ + r₂ = r - 1)
    (h₁ : c₁ - r₁ = 4) (h₂ : c₂ - r₂ = 4) :
    c - r = 4 := by
  omega


end StatMech.Onsager.GroundUp
