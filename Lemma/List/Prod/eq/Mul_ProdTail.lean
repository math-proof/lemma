import sympy.Basic


@[main]
private lemma main
  [Monoid α]
  {l : List α} :
-- imply
  l.prod = l.headD 1 * l.tail.prod := by
-- proof
  induction l <;> simp


-- created on 2024-07-01
