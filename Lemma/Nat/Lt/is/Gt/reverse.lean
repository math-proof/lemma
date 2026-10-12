import Mathlib.Basic.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {x a : ℝ} :
-- imply
  x < a ↔ a > x :=
-- proof
  Iff.rfl


-- created on 2020-01-10
