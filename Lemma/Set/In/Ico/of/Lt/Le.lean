import sympy.Basic


@[path]
private lemma main
  {a b x : ℤ}
-- given
  (h₀ : b < x)
  (h₁ : x ≤ a) :
-- imply
  x ∈ Set.Ico (b + 1) (a + 1) :=
-- proof
  Set.mem_Ico.mpr ⟨by omega, by omega⟩


-- created on 2021-05-31
