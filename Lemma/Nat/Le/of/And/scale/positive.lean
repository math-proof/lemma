import Mathlib.Basic.Real.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b c : ℝ}
-- given
  (hle : a ≤ b)
  (hpos : 0 < c) :
-- imply
  a * c ≤ b * c :=
-- proof
  mul_le_mul_of_nonneg_right hle (le_of_lt hpos)


-- created on 2019-08-19
