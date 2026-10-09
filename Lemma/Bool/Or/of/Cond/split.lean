import sympy.Basic


@[path]
private lemma main
  {p c : Prop} :
-- imply
  p → (p ∧ ¬c) ∨ c := by
-- proof
  intro hp
  by_cases hc : c
  · exact Or.inr hc
  · exact Or.inl ⟨hp, hc⟩


-- created on 2021-08-08
