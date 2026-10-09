import sympy.Basic


@[path]
private lemma main
  {p q r : Prop}
-- given
  (h₀ : q ∧ r → p)
  (h₁ : q) :
-- imply
  r → p :=
-- proof
  fun hr => h₀ ⟨h₁, hr⟩


-- created on 2019-03-03
