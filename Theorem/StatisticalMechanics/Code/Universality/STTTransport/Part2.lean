/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
import Def.StatisticalMechanics.Code.Universality.STTTransport
open SimpleGraph


namespace StatMech

namespace Universality

variable {V : Type*}


theorem triCell_adj_BC (A B C : V) (ω : LocalConfig) (h : ω.1 = true) (hBC : B ≠ C) :
    (triCell A B C ω).Adj B C := by
  unfold triCell; rw [fromEdgeSet_adj]; exact ⟨Or.inl ⟨h, rfl⟩, hBC⟩

theorem triCell_adj_AC (A B C : V) (ω : LocalConfig) (h : ω.2.1 = true) (hAC : A ≠ C) :
    (triCell A B C ω).Adj A C := by
  unfold triCell; rw [fromEdgeSet_adj]; exact ⟨Or.inr (Or.inl ⟨h, rfl⟩), hAC⟩

theorem triCell_adj_AB (A B C : V) (ω : LocalConfig) (h : ω.2.2 = true) (hAB : A ≠ B) :
    (triCell A B C ω).Adj A B := by
  unfold triCell; rw [fromEdgeSet_adj]; exact ⟨Or.inr (Or.inr ⟨h, rfl⟩), hAB⟩


theorem triCell_adj_imp (A B C : V) (ω : LocalConfig) {x y : V}
    (h : (triCell A B C ω).Adj x y) :
    (ω.1 ∧ s(x, y) = s(B, C)) ∨ (ω.2.1 ∧ s(x, y) = s(A, C)) ∨ (ω.2.2 ∧ s(x, y) = s(A, B)) := by
  unfold triCell at h
  rw [fromEdgeSet_adj] at h
  simpa using h.1


theorem starCell_adj_OA (A B C O : V) (ω : LocalConfig) (h : ω.1 = true) (hOA : O ≠ A) :
    (starCell A B C O ω).Adj O A := by
  unfold starCell; rw [fromEdgeSet_adj]; exact ⟨Or.inl ⟨h, rfl⟩, hOA⟩

theorem starCell_adj_OB (A B C O : V) (ω : LocalConfig) (h : ω.2.1 = true) (hOB : O ≠ B) :
    (starCell A B C O ω).Adj O B := by
  unfold starCell; rw [fromEdgeSet_adj]; exact ⟨Or.inr (Or.inl ⟨h, rfl⟩), hOB⟩

theorem starCell_adj_OC (A B C O : V) (ω : LocalConfig) (h : ω.2.2 = true) (hOC : O ≠ C) :
    (starCell A B C O ω).Adj O C := by
  unfold starCell; rw [fromEdgeSet_adj]; exact ⟨Or.inr (Or.inr ⟨h, rfl⟩), hOC⟩


theorem starCell_adj_imp (A B C O : V) (ω : LocalConfig) {x y : V}
    (h : (starCell A B C O ω).Adj x y) :
    (x = O ∧ ((y = A ∧ ω.1) ∨ (y = B ∧ ω.2.1) ∨ (y = C ∧ ω.2.2))) ∨
    (y = O ∧ ((x = A ∧ ω.1) ∨ (x = B ∧ ω.2.1) ∨ (x = C ∧ ω.2.2))) := by
  unfold starCell at h
  rw [fromEdgeSet_adj] at h
  obtain ⟨hmem, _⟩ := h
  simp only [Set.mem_setOf_eq] at hmem
  rcases hmem with ⟨hb, he⟩ | ⟨hb, he⟩ | ⟨hb, he⟩ <;>
    rw [Sym2.eq_iff] at he <;> rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all


variable (E : SimpleGraph V) {A B C : V}


theorem triCell_reach_BC (A B C : V) (ω : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (h : triBC ω = true) :
    (E ⊔ triCell A B C ω).Reachable B C := by
  unfold triBC at h; rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Adj.reachable (Or.inr (triCell_adj_BC A B C ω h hBC))
  · rw [Bool.and_eq_true] at h
    exact (Adj.reachable (Or.inr (triCell_adj_AB A B C ω h.2 hAB))).symm.trans
      (Adj.reachable (Or.inr (triCell_adj_AC A B C ω h.1 hAC)))


theorem triCell_reach_AC (A B C : V) (ω : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (h : triAC ω = true) :
    (E ⊔ triCell A B C ω).Reachable A C := by
  unfold triAC at h; rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Adj.reachable (Or.inr (triCell_adj_AC A B C ω h hAC))
  · rw [Bool.and_eq_true] at h
    exact (Adj.reachable (Or.inr (triCell_adj_AB A B C ω h.2 hAB))).trans
      (Adj.reachable (Or.inr (triCell_adj_BC A B C ω h.1 hBC)))


theorem triCell_reach_AB (A B C : V) (ω : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (h : triAB ω = true) :
    (E ⊔ triCell A B C ω).Reachable A B := by
  unfold triAB at h; rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Adj.reachable (Or.inr (triCell_adj_AB A B C ω h hAB))
  · rw [Bool.and_eq_true] at h
    exact (Adj.reachable (Or.inr (triCell_adj_AC A B C ω h.2 hAC))).trans
      (Adj.reachable (Or.inr (triCell_adj_BC A B C ω h.1 hBC))).symm


theorem starCell_reach_AB (A B C O : V) (ω : LocalConfig)
    (hOA : O ≠ A) (hOB : O ≠ B) (h : starAB ω = true) :
    (E ⊔ starCell A B C O ω).Reachable A B := by
  unfold starAB at h; rw [Bool.and_eq_true] at h
  exact (Adj.reachable (Or.inr (starCell_adj_OA A B C O ω h.1 hOA))).symm.trans
    (Adj.reachable (Or.inr (starCell_adj_OB A B C O ω h.2 hOB)))


theorem starCell_reach_AC (A B C O : V) (ω : LocalConfig)
    (hOA : O ≠ A) (hOC : O ≠ C) (h : starAC ω = true) :
    (E ⊔ starCell A B C O ω).Reachable A C := by
  unfold starAC at h; rw [Bool.and_eq_true] at h
  exact (Adj.reachable (Or.inr (starCell_adj_OA A B C O ω h.1 hOA))).symm.trans
    (Adj.reachable (Or.inr (starCell_adj_OC A B C O ω h.2 hOC)))


theorem starCell_reach_BC (A B C O : V) (ω : LocalConfig)
    (hOB : O ≠ B) (hOC : O ≠ C) (h : starBC ω = true) :
    (E ⊔ starCell A B C O ω).Reachable B C := by
  unfold starBC at h; rw [Bool.and_eq_true] at h
  exact (Adj.reachable (Or.inr (starCell_adj_OB A B C O ω h.1 hOB))).symm.trans
    (Adj.reachable (Or.inr (starCell_adj_OC A B C O ω h.2 hOC)))


end Universality
end StatMech
