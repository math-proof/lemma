import sympy.Basic


@[main]
private lemma main
  {x a b : ℤ} :
-- imply
  a < x ∧ x < b ↔ x ∈ Set.Ico (a + 1) b := by
-- proof
  rw [Set.mem_Ico]
  omega


-- created on 2026-09-27
