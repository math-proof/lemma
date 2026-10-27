import Mathlib.Data.Int.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a x : ℤ}
  -- imply
  : x ≤ a ↔ x - 1 < a := by
  -- proof
  constructor <;> omega

-- created on 2022-01-28
