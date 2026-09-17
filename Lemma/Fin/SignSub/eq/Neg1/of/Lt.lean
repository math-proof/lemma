import sympy.functions.elementary.integers
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {j i : Fin n}
-- given
  (h : j < i) :
-- imply
  (j - i : ℤ).sign = -1 := by
-- proof
  apply Int.sign_eq_neg_one_of_neg
  have : (j : ℕ) < (i : ℕ) := h
  omega


-- created on 2026-09-17
-- updated on 2026-09-17
