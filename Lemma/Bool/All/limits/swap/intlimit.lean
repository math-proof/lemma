import sympy.Basic


@[path]
private lemma main
  {n d a : ℕ}
  {f : ℕ → Prop}
  {g : ℕ → ℕ → Prop} :
-- imply
  (∀ j ∈ Finset.Ico (a + 1) n, ∀ i ∈ Finset.Ico (a + d) (j + d), f i ∧ g i j) ↔
    ∀ i ∈ Finset.Ico (a + d) (n + d - 1), ∀ j ∈ Finset.Ico (max (a + 1) (i - d + 1)) n, f i ∧ g i j := by
-- proof
  sorry


-- created on 2026-10-11
