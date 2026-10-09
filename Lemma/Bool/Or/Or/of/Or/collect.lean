import sympy.Basic


@[path]
private lemma main
  {p q r c : Prop}
-- given
  (h₁ : p ∨ c)
  (h₂ : q ∨ c)
  (h₃ : r ∨ c) :
-- imply
  c ∨ p ∧ q ∧ r := by
-- proof
  by_cases hc : c
  · exact Or.inl hc
  · obtain hp | hc := h₁ <;> obtain hq | hc := h₂ <;> obtain hr | hc := h₃ <;> tauto


-- created on 2021-09-09
