import sympy.Basic


@[path]
private lemma main
  [Mul α]
  {a b x y : α}
-- given
  (h₀ : a = b)
  (h₁ : x = y) :
-- imply
  x * a = y * b := by
-- proof
  rw [h₀, h₁]


-- created on 2019-03-25
