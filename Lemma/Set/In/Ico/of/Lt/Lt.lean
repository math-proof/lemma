import sympy.Basic


@[main]
private lemma main
  {a b x : ℤ}
-- given
  (h₀ : b < x)
  (h₁ : x < a) :
-- imply
  x ∈ Set.Ico (b + 1) a :=
-- proof
  Set.mem_Ico.mpr ⟨by omega, h₁⟩


-- created on 2021-06-02
