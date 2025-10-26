import sympy.Basic


@[main]
private lemma main
  [Group α]
  {a : α} :
-- imply
  a * a⁻¹ = 1 := by
-- proof
  apply mul_inv_cancel


-- created on 2024-11-25
