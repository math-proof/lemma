import sympy.Basic


@[path]
private lemma main
  {e a b : ℤ}
-- given
  (h : e < a ∨ e ≥ b) :
-- imply
  e ∉ Set.Ico a b := by
-- proof
  rw [Set.mem_Ico]
  omega


-- created on 2021-06-06
