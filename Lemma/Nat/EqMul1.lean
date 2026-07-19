import sympy.Basic


@[main]
private lemma main
  [MulOneClass M]
-- given
  (a : M) :
-- imply
  1 * a = a := by
-- proof
  rw [one_mul]


-- created on 2024-07-01
-- updated on 2026-07-19
