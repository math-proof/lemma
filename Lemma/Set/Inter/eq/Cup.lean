import sympy.Basic
import Mathlib


@[path]
private lemma main
  {f : ℕ → Set α}
  {x : Set α}
  {n : ℕ} :
-- imply
  (⋃ k ∈ Finset.range n, f k) ∩ x = ⋃ k ∈ Finset.range n, f k ∩ x := by
-- proof
  ext y
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  ·
    rintro ⟨⟨k, hk, hyf⟩, hyx⟩
    exact ⟨k, hk, hyf, hyx⟩
  ·
    rintro ⟨k, hk, hyf, hyx⟩
    exact ⟨⟨k, hk, hyf⟩, hyx⟩


-- created on 2021-02-09
