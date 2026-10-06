import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {a b c : ℝ}
  -- given
  (hlt : a < b)
  (hpos : 0 < c)
  -- imply
  : a / c < b / c := by
  -- proof
  exact div_lt_div_of_pos_right hlt hpos

-- created on 2023-03-26
