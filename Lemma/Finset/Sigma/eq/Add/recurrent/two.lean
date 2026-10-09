import Mathlib
import sympy.Basic


@[path]
private lemma main
  {n k : ℕ}
  {x : ℕ → ℂ}
-- given
  (hk : 2 ≤ k) :
-- imply
  (∑ t ∈ (Finset.range (n + 1)).powersetCard k, t.prod x)
    = x n * (∑ t ∈ (Finset.range n).powersetCard (k - 1), t.prod x)
      + (∑ t ∈ (Finset.range n).powersetCard k, t.prod x) := by
-- proof
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hn_range : n ∉ Finset.range n := Finset.mem_range.not.mpr (Nat.lt_irrefl n)
  rw [Finset.range_add_one, Finset.powersetCard_succ_insert hn_range]
  have hdisj : Disjoint ((Finset.range n).powersetCard (k' + 1))
    (((Finset.range n).powersetCard k').image (insert n)) := by
    apply Finset.disjoint_right.mpr
    intro t hmem hmem2
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hmem
    exact hn_range ((Finset.mem_powersetCard.mp hmem2).1 (Finset.mem_insert_self n u))
  rw [Finset.sum_union hdisj]
  have hinj : Set.InjOn (insert n) ((Finset.range n).powersetCard k' : Set (Finset ℕ)) := by
    intro u hu u' hu' hab
    have hnu : n ∉ u := fun h => hn_range ((Finset.mem_powersetCard.mp hu).1 h)
    have hnu' : n ∉ u' := fun h => hn_range ((Finset.mem_powersetCard.mp hu').1 h)
    apply Finset.ext
    intro a
    constructor
    ·
      intro ha
      cases Finset.mem_insert.mp (hab ▸ Finset.mem_insert_of_mem ha : a ∈ insert n u') with
      | inl h => exact absurd (h ▸ ha : n ∈ u) hnu
      | inr h => exact h
    ·
      intro ha
      cases Finset.mem_insert.mp (hab.symm ▸ Finset.mem_insert_of_mem ha : a ∈ insert n u) with
      | inl h => exact absurd (h ▸ ha : n ∈ u') hnu'
      | inr h => exact h
  rw [Finset.sum_image hinj]
  have hprod : ∀ t ∈ (Finset.range n).powersetCard k', (insert n t).prod x = x n * t.prod x := by
    intro t ht
    rw [Finset.prod_insert
      (fun hmem ↦ hn_range ((Finset.mem_powersetCard.mp ht).1 hmem))]
  rw [Finset.sum_congr rfl hprod, Finset.mul_sum]
  ring


-- created on 2026-10-07
