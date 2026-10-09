import sympy.Basic


@[path]
private lemma main
  {p q c : Prop}
-- given
  (h₀ : p ∧ c → q)
  (h₁ : p ∧ ¬c → q) :
-- imply
  p → q := by
-- proof
  classical
  intro hp
  if hc : c then
    exact h₀ ⟨hp, hc⟩
  else
    exact h₁ ⟨hp, hc⟩


-- created on 2020-09-21
