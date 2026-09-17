import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {j i : Fin n} :
-- imply
  (j - i : ℤ).natAbs < n := by
-- proof
  have := j.isLt
  have := i.isLt
  omega


-- created on 2026-09-17
-- updated on 2026-09-17
