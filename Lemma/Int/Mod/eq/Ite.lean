import sympy.Basic


@[path]
private lemma main
  {n : ℤ} :
-- imply
  n % 2 = if n % 2 = 0 then 0 else 1 := by
-- proof
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> simp [h]


-- created on 2022-01-20
