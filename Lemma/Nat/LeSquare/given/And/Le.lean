import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (ha : 0 ≤ a)
  (h₀ : x ≤ Real.sqrt a)
  (h₁ : -Real.sqrt a ≤ x) :
-- imply
  x ^ 2 ≤ a :=
-- proof
  (Real.sq_le ha).mpr ⟨h₁, h₀⟩


-- created on 2023-06-18
