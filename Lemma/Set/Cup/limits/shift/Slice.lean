import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b k : ℤ}
  {f : ℤ → Set α} :
-- imply
  (⋃ i ∈ Finset.Ico a b, f (i + k)) = ⋃ i ∈ Finset.Ico (a + k) (b + k), f i := by
-- proof
  ext x
  simp only [Set.mem_iUnion]
  refine ⟨?_, ?_⟩
  ·
    intro h
    obtain ⟨i, hi, hx⟩ := h
    refine ⟨i + k, ?_, by simpa using hx⟩
    rw [Finset.mem_Ico] at hi ⊢
    omega
  ·
    intro h
    obtain ⟨i, hi, hx⟩ := h
    refine ⟨i - k, ?_, ?_⟩
    ·
      rw [Finset.mem_Ico] at hi ⊢
      omega
    ·
      simpa [sub_add_cancel] using hx


-- created on 2023-07-02
-- updated on 2026-10-17
