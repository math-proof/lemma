import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {p : ℕ → ℕ → Prop} :
-- imply
  (∃ i < n, ∃ j < n, p i j) ↔ ∃ j < n, ∃ i < n, p i j := by
-- proof
  constructor
  ·
    intro h
    obtain ⟨i, hi, j, hj, hp⟩ := h
    exact ⟨j, hj, i, hi, hp⟩
  ·
    intro h
    obtain ⟨j, hj, i, hi, hp⟩ := h
    exact ⟨i, hi, j, hj, hp⟩


-- created on 2026-10-11
-- updated on 2026-10-17
