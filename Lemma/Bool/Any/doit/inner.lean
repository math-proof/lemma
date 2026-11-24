import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.limits.swap.subst


@[path]
private lemma main
  {a m : ℕ}
  {p : ℕ → ℕ → Prop} :
-- imply
  (∃ i < m, ∃ j ∈ Finset.Ico a (a + 2), p i j) ↔ ∃ i < m, p i a ∨ p i (a + 1) := by
-- proof
  constructor
  ·
    rintro ⟨i, hi, j, hj, h⟩
    simp only [Finset.mem_Ico] at hj
    rcases (show j = a ∨ j = a + 1 by omega) with rfl | rfl
    ·
      exact ⟨i, hi, Or.inl h⟩
    ·
      exact ⟨i, hi, Or.inr h⟩
  ·
    rintro ⟨i, hi, h | h⟩
    ·
      exact ⟨i, hi, a, by simp, h⟩
    ·
      exact ⟨i, hi, a + 1, by simp, h⟩




-- created on 2026-09-27
-- updated on 2026-11-24
