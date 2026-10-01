import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {e a b : ℝ}
-- given
  (h : e < a ∨ e ≥ b) :
-- imply
  e ∉ Set.Ico a b := by
-- proof
  rintro ⟨h₁, h₂⟩
  rcases h with h | h <;> linarith


-- created on 2019-07-08
