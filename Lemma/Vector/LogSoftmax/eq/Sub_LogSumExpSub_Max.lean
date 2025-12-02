import sympy.Basic
import sympy.vector.functions


@[main]
private lemma main
  [NeZero n]
  [LT α] [DecidableLT α]
  [Div α] [Exp α]
  [Log α]
-- given
  (x : List.Vector α n)
  (d : ℕ) :
-- imply
  log x.softmax = x - x.max - log (exp (x - x.max).sum) := by
-- proof
  sorry


-- created on 2025-11-30
-- updated on 2025-12-02
