/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WindingAssembly.Part2
import Def.StatisticalMechanics.Code.Onsager.CornerCount.Part2


namespace StatMech.Onsager.CornerCount

open StatMech.Onsager.WindingAssembly

open StatMech.Onsager.SplitConstruction


theorem cornerBalanceL_eq (V : List Pt)
    (h : ∀ t ∈ turnList V, t = -1 ∨ t = 0 ∨ t = 1) :
    cornerBalanceL V = ccCount V - rcCount V := by
  unfold cornerBalanceL ccCount rcCount
  exact sum_eq_ccrc (turnList V) h


theorem mem_zipWith_imp {α β γ : Type*} (f : α → β → γ) :
    ∀ (l₁ : List α) (l₂ : List β) (c : γ), c ∈ List.zipWith f l₁ l₂ →
      ∃ a b, a ∈ l₁ ∧ b ∈ l₂ ∧ c = f a b
  | [], _, c, hc => by simp at hc
  | _, [], c, hc => by simp at hc
  | a :: l₁, b :: l₂, c, hc => by
    rw [List.zipWith_cons_cons, List.mem_cons] at hc
    rcases hc with hc | hc
    · exact ⟨a, b, List.mem_cons_self .., List.mem_cons_self .., hc⟩
    · obtain ⟨a', b', ha', hb', hc'⟩ := mem_zipWith_imp f l₁ l₂ c hc
      exact ⟨a', b', List.mem_cons_of_mem _ ha', List.mem_cons_of_mem _ hb', hc'⟩


end StatMech.Onsager.CornerCount
