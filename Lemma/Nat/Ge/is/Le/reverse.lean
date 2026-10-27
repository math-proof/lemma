import Mathlib.Data.Int.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x a : ℤ}
  -- imply
  : a ≤ x ↔ a ≤ x := by
  -- proof
  rfl

-- created on 2019-06-05
