import sympy.Basic


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d ≠ 0)
  (n : ℤ):
-- imply
  n % d ≥ 0 := by
-- proof
  apply Int.emod_nonneg -- Apply the theorem `Int.emod_nonneg` which states that for any integers `n` and `d ≠ 0`, `n % d ≥ 0`.
  assumption


-- created on 2025-03-18
-- updated on 2025-03-29
