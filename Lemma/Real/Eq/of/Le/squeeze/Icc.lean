import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h_left : b ≤ x)
  (_h_right : x ≤ a)
  (hle : x ≤ b) :
-- imply
  x = b := by
-- proof
  exact le_antisymm hle h_left


-- created on 2020-05-06
