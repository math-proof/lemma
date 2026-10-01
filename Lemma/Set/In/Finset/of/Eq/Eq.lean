import sympy.Basic


@[main]
private lemma main
  {x a b : ℤ}
-- given
  (h₀ : x = a)
  (h₁ : x = b) :
-- imply
  x ∈ ({a} ∩ {b} : Set ℤ) :=
-- proof
  Set.mem_inter h₀ h₁


-- created on 2020-12-23
