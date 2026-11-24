import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.is.Or.doit.outer
import Lemma.Bool.Any.is.Or.doit.outer.setlimit
import Lemma.Bool.Any.is.Or.doit.setlimit


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


-- created on 2026-09-27
