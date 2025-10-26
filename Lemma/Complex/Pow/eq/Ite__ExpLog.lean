import sympy.Basic


@[main]
private lemma main
  {x y : ℂ} :
-- imply
  x ^ y =
    if x = 0 then
      if y = 0 then
        1
      else
        0
    else
      (x.log * y).exp := by
-- proof
  rw [← Complex.cpow_eq_pow]
  rw [Complex.cpow]


-- created on 2025-03-01
