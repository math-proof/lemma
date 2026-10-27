import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a : ℤ}
  {f : ℤ → Set α} :
-- imply
  (⋃ i ∈ Finset.Ico (-a) (a + 1), f i) = ⋃ i ∈ Finset.Ico (-a) (a + 1), f (-i) := by
-- proof
  ext x
  simp only [Set.mem_iUnion]
  refine ⟨?_, ?_⟩
  ·
    intro h
    obtain ⟨i, hi, hx⟩ := h
    refine ⟨-i, ?_, by simpa using hx⟩
    rw [Finset.mem_Ico] at hi ⊢
    omega
  ·
    intro h
    obtain ⟨i, hi, hx⟩ := h
    refine ⟨-i, ?_, by simpa using hx⟩
    rw [Finset.mem_Ico] at hi ⊢
    omega


-- created on 2021-02-08
-- updated on 2026-10-26
