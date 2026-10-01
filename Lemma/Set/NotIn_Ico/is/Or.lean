import sympy.Basic


@[main]
private lemma main
  {e a b : ℤ} :
-- imply
  e ∉ Set.Ico a b ↔ e < a ∨ e ≥ b := by
-- proof
  rw [Set.mem_Ico]
  omega


-- created on 2026-09-27
