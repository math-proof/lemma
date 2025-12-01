import sympy.tensor.functions
import sympy.Basic


@[main]
private lemma main
  -- given
  (x : List.Vector α n)
  (d : ℕ) :
-- imply
  (x.softmax d).log = x - x.max - log (exp (x - x.max).sum) := by
-- proof
  sorry


-- created on 2025-11-30
