import Mathlib.Data.Int.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x a : ℤ}
  -- imply
  : x < a ↔ a ≥ x + 1 := by
  -- proof
  constructor <;> omega

-- created on 2021-12-17
