import sympy.Basic


@[main]
private lemma main
  [Monoid α]
  -- given
  (s : List α) :
-- imply
  s.prod = s.headD 1 * s.tail.prod := by
-- proof
  induction s <;>
    simp


-- created on 2024-07-01
