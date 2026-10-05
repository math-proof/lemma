import sympy.Basic


@[main]
private lemma main
  {a b x : ℤ}
-- given
  (h₀ : a < x)
  (h₁ : x < b) :
-- imply
  x ∈ Set.Ico (a + 1) b :=
-- proof
  Set.mem_Ico.mpr ⟨by omega, h₁⟩


-- created on 2021-05-29
