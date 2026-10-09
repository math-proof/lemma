import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {g h : ℝ → ℝ}
-- given
  (_h₀ : x ∈ Set.Ioi 0)
  (h₁ : g x = h x) :
-- imply
  g x / x = h x / x := by
-- proof
  rw [h₁]


-- created on 2023-06-06
