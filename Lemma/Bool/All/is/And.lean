import sympy.Basic


@[path]
private lemma doit.outer
  {x : ℤ → ℤ → ℝ}
  {f : ℤ → ℤ}
  {a : ℤ} :
-- imply
  (∀ i ∈ Set.Ico a (a + 2), ∀ j ∈ Set.Ico 0 (f i), x i j > 0) ↔ (∀ j ∈ Set.Ico 0 (f a), x a j > 0) ∧ ∀ j ∈ Set.Ico 0 (f (a + 1)), x (a + 1) j > 0 := by
-- proof
  constructor
  ·
    intro h
    exact ⟨h a (by simp only [Set.mem_Ico]; omega), h (a + 1) (by simp only [Set.mem_Ico]; omega)⟩
  ·
    rintro ⟨h₀, h₁⟩ i hi
    simp only [Set.mem_Ico] at hi
    obtain rfl | rfl : i = a ∨ i = a + 1 := by omega
    ·
      exact h₀
    ·
      exact h₁


@[path]
private lemma doit.outer.setlimit
  {x : ℤ → ℤ → ℝ}
  {f : ℤ → ℤ}
  {a b : ℤ} :
-- imply
  (∀ i ∈ ({a, b} : Set ℤ), ∀ j ∈ Set.Ico 0 (f i), x i j > 0) ↔ (∀ j ∈ Set.Ico 0 (f a), x a j > 0) ∧ ∀ j ∈ Set.Ico 0 (f b), x b j > 0 := by
-- proof
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]


-- created on 2026-09-27
