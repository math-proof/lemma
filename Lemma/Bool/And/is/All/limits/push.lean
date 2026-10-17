import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {p : ℕ → Prop} :
-- imply
  ((∀ i < n, p i) ∧ p n ∧ p (n + 1)) ↔ ∀ i < n + 2, p i := by
-- proof
  constructor
  ·
    intro h i hi
    obtain ⟨hall, hn, hn1⟩ := h
    if hlt : i < n then
      exact hall i hlt
    else if heq : i = n then
      simpa [heq] using hn
    else
      have : i = n + 1 := by omega
      simpa [this] using hn1
  ·
    intro h
    exact ⟨fun i hi => h i (by omega), h n (by omega), h (n + 1) (by omega)⟩


-- created on 2026-10-11
-- updated on 2026-10-17
