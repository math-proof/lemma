import sympy.functions.elementary.integers
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {j i : Fin n}
-- given
  (h : j = i) :
-- imply
  (j - i : ℤ).sign = 0 := by
-- proof
  simp [h]


-- created on 2026-09-17
-- updated on 2026-09-17
