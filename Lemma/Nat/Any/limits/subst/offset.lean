import sympy.Basic


@[path]
private lemma main
  {f : ℤ → Prop}
  {a b d : ℤ} :
-- imply
  (∃ i ∈ Set.Ico a b, f i) ↔ ∃ i ∈ Set.Ico (a + d) (b + d), f (i - d) := by
-- proof
  constructor
  ·
    intro h
    obtain ⟨i, hi, hf⟩ := h
    refine ⟨i + d, ?_, by simpa [add_sub_cancel_right] using hf⟩
    simp only [Set.mem_Ico] at hi ⊢
    omega
  ·
    intro h
    obtain ⟨i, hi, hf⟩ := h
    refine ⟨i - d, ?_, hf⟩
    simp only [Set.mem_Ico] at hi ⊢
    omega


-- created on 2019-02-21
-- updated on 2026-10-17
