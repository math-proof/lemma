import Mathlib.Data.Int.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℤ}
  -- given
  (h : y ≤ x)
  -- imply
  : 0 ≤ x - y := by
  -- proof
  exact sub_nonneg.mpr h

-- created on 2018-07-03
-- updated on 2026-10-26
