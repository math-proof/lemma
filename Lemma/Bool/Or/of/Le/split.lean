import sympy.Basic


@[main]
private lemma main
  {x y z : ℝ} :
-- imply
  x ≤ y → (x ≤ y ∧ z ≤ x) ∨ x < z := by
-- proof
  intro hxy
  by_cases h : z ≤ x
  · exact Or.inl ⟨hxy, h⟩
  · have h' : x < z := by linarith
    exact Or.inr h'


-- created on 2019-11-18
