import sympy.Basic


@[path]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : x ≥ a)
  (h₁ : y ≥ b) :
-- imply
  (x - a) * (y - b) ≥ 0 :=
-- proof
  mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr h₁)


-- created on 2019-05-19
