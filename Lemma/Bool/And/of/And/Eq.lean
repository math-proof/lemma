import sympy.Basic


@[path]
private lemma continued.given
  {a b c m : α}
-- given
  (h₀ : a = m)
  (h₁ : b = m)
  (h₂ : c = m) :
-- imply
  a = b ∧ b = c :=
-- proof
  ⟨h₀.trans h₁.symm, h₁.trans h₂.symm⟩


-- created on 2021-11-24
