import sympy.Basic


@[path]
private lemma main
-- given
  (s : Set α)
  (a : α)
  (p : α → Prop) :
-- imply
  (∀ ι ∈ (Set.insert a s), p ι) ↔ p a ∧ ∀ ι ∈ s, p ι := by
-- proof
  simp [Set.insert]


@[path]
private lemma doit
  {x : ℤ → ℤ → ℝ}
  {m a b : ℤ} :
-- imply
  (∀ i ∈ Set.Ico 0 m, ∀ j ∈ ({a, b} : Set ℤ), x i j > 0) ↔ ∀ i ∈ Set.Ico 0 m, x i a > 0 ∧ x i b > 0 := by
-- proof
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]


-- created on 2018-03-29
-- updated on 2026-09-27
