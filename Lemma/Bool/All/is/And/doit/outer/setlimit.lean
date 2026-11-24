import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℤ → ℤ → ℝ}
  {f : ℤ → ℤ}
  {a b : ℤ} :
-- imply
  (∀ i ∈ ({a, b} : Set ℤ), ∀ j ∈ Set.Ico 0 (f i), x i j > 0) ↔ (∀ j ∈ Set.Ico 0 (f a), x a j > 0) ∧ ∀ j ∈ Set.Ico 0 (f b), x b j > 0 := by
-- proof
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]




-- created on 2026-09-27
-- updated on 2026-11-24
