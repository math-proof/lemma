import Mathlib.Basic.Real.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x a : ℝ} :
-- imply
  x ≤ a ↔ x ≤ a :=
-- proof
  Iff.rfl


-- created on 2019-11-26
