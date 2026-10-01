import sympy.sets.sets
import sympy.Basic


@[main]
private lemma reverse
  {x a : ℝ} :
-- imply
  x > a ↔ a < x := by
-- proof
  exact Iff.rfl


-- created on 2019-08-02
