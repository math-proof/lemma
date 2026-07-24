import sympy.Basic


@[main]
private lemma main
  [Mul α]
  {a b x y : α}
-- given
  (h₀ : a = b)
  (h₁ : x = y) :
-- imply
  a * x = b * y := by
-- proof
  congr


-- created on 2024-07-01
