import sympy.Basic


@[main, comm]
private lemma main
  [AddMonoidWithOne α]
  {a : ℕ} :
-- imply
  ((a + 1 : ℕ) : α) = a + 1 := by
-- proof
  simp


-- created on 2025-05-23
