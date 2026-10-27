import Mathlib.Basic.Real.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x a : ℝ} :
-- imply
  x < a ↔ a > x :=
-- proof
  Iff.rfl


-- created on 2020-01-10
