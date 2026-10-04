import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : b < x)
  (h₁ : x ≤ a) :
-- imply
  x ∈ Set.Ioc b a :=
-- proof
  Set.mem_Ioc.mpr ⟨h₀, h₁⟩


-- created on 2021-05-31
