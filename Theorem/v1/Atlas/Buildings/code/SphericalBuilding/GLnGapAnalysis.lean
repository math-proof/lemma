/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnGapAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnPanelExtension


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- `List.insertIdx` decomposed as `take ++ a :: drop`. -/
theorem insertIdx_eq_take_append_drop' {α : Type*} {l : List α} {w : α} {i : ℕ}
    (hi : i ≤ l.length) :
    l.insertIdx i w = l.take i ++ w :: l.drop i := by
  induction l generalizing i with
  | nil => simp at hi; subst hi; simp [List.insertIdx]
  | cons a t ih =>
    cases i with
    | zero => simp [List.insertIdx]
    | succ j =>
      simp only [List.insertIdx, List.take, List.drop, List.cons_append]
      exact congrArg (List.cons a) (ih (by simp at hi; omega))

/-- Inserting an element at index $i$ preserves `Pairwise R`, given the appropriate relation
to elements before and after position $i$. -/
theorem pairwise_insertIdx_of_pairwise {α : Type*} {R : α → α → Prop}
    {l : List α} {w : α} {i : ℕ}
    (hpw : l.Pairwise R)
    (hi : i ≤ l.length)
    (hbefore : ∀ x ∈ l.take i, R x w)
    (hafter : ∀ y ∈ l.drop i, R w y) :
    (l.insertIdx i w).Pairwise R := by
  rw [insertIdx_eq_take_append_drop' hi]
  show (l.take i ++ ([w] ++ l.drop i)).Pairwise R
  have hpw' : (l.take i ++ l.drop i).Pairwise R := by
    rw [List.take_append_drop]; exact hpw
  rw [← List.append_assoc]
  rw [List.pairwise_append] at hpw' ⊢
  obtain ⟨hpw1, hpw2, hpw12⟩ := hpw'
  refine ⟨?_, hpw2, ?_⟩
  · rw [List.pairwise_append]
    exact ⟨hpw1, List.pairwise_singleton R w,
           fun a ha b hb => by simp at hb; subst hb; exact hbefore a ha⟩
  · intro a ha b hb
    simp [List.mem_append] at ha
    cases ha with
    | inl h => exact hpw12 a h b hb
    | inr h => simp at h; subst h; exact hafter b hb

/-- Inserting an element preserves the `IsChain R` property under the same conditions. -/
theorem isChain_insertIdx_of_isChain {α : Type*} {R : α → α → Prop} [Trans R R R]
    {l : List α} {w : α} {i : ℕ}
    (hch : l.IsChain R)
    (hi : i ≤ l.length)
    (hbefore : ∀ x ∈ l.take i, R x w)
    (hafter : ∀ y ∈ l.drop i, R w y) :
    (l.insertIdx i w).IsChain R := by
  rw [List.isChain_iff_pairwise] at hch ⊢
  exact pairwise_insertIdx_of_pairwise hch hi hbefore hafter

end GLnBuilding
