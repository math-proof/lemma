import Mathlib.Basic.Real.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : ℝ} :
-- imply
  b < a ↔ b < a :=
-- proof
  Iff.rfl


-- created on 2019-08-02
