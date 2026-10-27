import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a : ℤ}
  {f : ℤ → ℤ}
  {p : ℤ → ℤ → Prop} :
-- imply
  (∀ i ∈ Set.Ico a (a + 2), ∀ j ∈ Set.Ico 0 (f i), p i j) ↔
    (∀ j ∈ Set.Ico 0 (f a), p a j) ∧ ∀ j ∈ Set.Ico 0 (f (a + 1)), p (a + 1) j := by
-- proof
  constructor
  ·
    intro h
    exact ⟨h a (by simp only [Set.mem_Ico]; omega), h (a + 1) (by simp only [Set.mem_Ico]; omega)⟩
  ·
    rintro ⟨h₀, h₁⟩ i hi
    simp only [Set.mem_Ico] at hi
    obtain rfl | rfl : i = a ∨ i = a + 1 := by omega
    · apply h₀
    · apply h₁


-- created on 2026-10-11
-- updated on 2026-10-26
