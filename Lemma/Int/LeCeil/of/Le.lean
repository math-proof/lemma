import Mathlib.Data.Int.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℤ}
  {y : ℝ}
  -- given
  (h : y ≤ (x : ℝ))
  -- imply
  : ⌈y⌉ ≤ x := by
  -- proof
  exact Int.ceil_le.mpr h

-- created on 2018-05-22
