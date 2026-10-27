import Mathlib.Data.Int.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x a : ℤ}
  -- imply
  : x < a ↔ x + 1 ≤ a := by
  -- proof
  constructor <;> omega

-- created on 2022-01-02
