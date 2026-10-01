import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b M : ℝ}
-- given
  (h : min a b = M) :
-- imply
  M ≤ a ∧ M ≤ b := by
-- proof
  exact ⟨h ▸ min_le_left a b, h ▸ min_le_right a b⟩


-- created on 2019-04-25
