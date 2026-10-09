import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {S : Set ℝ}
-- given
  (h : x ∈ S)
  (h₀ : (0 : ℝ) ∉ S) :
-- imply
  x ≠ 0 := by
-- proof
  intro hx
  exact h₀ (hx ▸ h)


-- created on 2020-05-13
