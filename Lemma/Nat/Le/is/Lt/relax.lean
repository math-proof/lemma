import Mathlib.Data.Int.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : ℤ}
  -- imply
  : a ≤ b ↔ a < b + 1 := by
  -- proof
  constructor <;> omega

-- created on 2023-11-05
