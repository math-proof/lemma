import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b M : ℝ}
-- given
  (h : max a b = M) :
-- imply
  M ≥ a ∧ M ≥ b := by
-- proof
  exact ⟨h ▸ le_max_left a b, h ▸ le_max_right a b⟩


-- created on 2019-04-24
