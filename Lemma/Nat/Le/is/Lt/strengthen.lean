import Mathlib.Data.Int.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : ℤ}
  -- imply
  : a ≤ b ↔ a - 1 < b := by
  -- proof
  constructor <;> omega

-- created on 2022-01-28
