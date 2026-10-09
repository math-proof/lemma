import sympy.Basic


@[path]
private lemma doit
  {x : ℤ → ℝ}
  {a : ℤ} :
-- imply
  (∃ i ∈ Set.Ico a (a + 2), x i > 0) ↔ x a > 0 ∨ x (a + 1) > 0 := by
-- proof
  constructor
  ·
    rintro ⟨i, hi, h⟩
    simp only [Set.mem_Ico] at hi
    obtain rfl | rfl : i = a ∨ i = a + 1 := by omega
    ·
      exact Or.inl h
    ·
      exact Or.inr h
  ·
    rintro (h | h)
    ·
      exact ⟨a, by simp only [Set.mem_Ico]; omega, h⟩
    ·
      exact ⟨a + 1, by simp only [Set.mem_Ico]; omega, h⟩


@[path]
private lemma doit.outer
  {x : ℕ → ℕ → ℝ}
  {f : ℕ → ℕ} :
-- imply
  ∑ i ∈ Finset.range 2, ∑ j ∈ Finset.range (f i), x i j = ∑ j ∈ Finset.range (f 0), x 0 j + ∑ j ∈ Finset.range (f 1), x 1 j := by
-- proof
  simp [Finset.sum_range_succ]


@[path]
private lemma doit.outer.setlimit
  [DecidableEq ι]
  {x : ι → ℕ → ℝ}
  {f : ι → ℕ}
  {a b : ι}
-- given
  (h : a ≠ b) :
-- imply
  ∑ i ∈ ({a, b} : Finset ι), ∑ j ∈ Finset.range (f i), x i j = ∑ j ∈ Finset.range (f a), x a j + ∑ j ∈ Finset.range (f b), x b j := by
-- proof
  rw [Finset.sum_pair h]


@[path]
private lemma doit.setlimit
  {x : ℤ → ℝ}
  {a b : ℤ} :
-- imply
  (∃ i ∈ ({a, b} : Set ℤ), x i > 0) ↔ x a > 0 ∨ x b > 0 := by
-- proof
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left]


-- created on 2026-09-27
