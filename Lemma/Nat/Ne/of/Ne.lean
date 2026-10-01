import sympy.sets.sets
import sympy.Basic


@[main]
private lemma reverse.given
  {a b : α}
-- given
  (h : a ≠ b) :
-- imply
  b ≠ a := by
-- proof
  exact h.symm


@[main]
private lemma reverse
  {a b : α}
-- given
  (h : a ≠ b) :
-- imply
  b ≠ a := by
-- proof
  exact h.symm


-- created on 2026-09-27
