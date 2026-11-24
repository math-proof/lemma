import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a m : ℕ}
  {p : ℕ → ℕ → Prop} :
-- imply
  (∀ i < m, ∀ j ∈ Finset.Ico a (a + 2), p i j) ↔ ∀ i < m, p i a ∧ p i (a + 1) := by
-- proof
  constructor
  ·
    intro h i hi
    exact ⟨h i hi a (by simp), h i hi (a + 1) (by simp)⟩
  ·
    intro h i hi j hj
    simp only [Finset.mem_Ico] at hj
    rcases (show j = a ∨ j = a + 1 by omega) with rfl | rfl
    ·
      exact (h i hi).1
    ·
      exact (h i hi).2


-- created on 2018-12-05
-- updated on 2026-11-24
