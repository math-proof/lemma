import sympy.functions.elementary.exponential


@[main, comm]
private lemma main
-- given
  (x : ℝ) :
-- imply
  Hyperreal.ofReal (exp x) = exp (Hyperreal.ofReal x) := by
-- proof
  rfl


-- created on 2026-07-28
