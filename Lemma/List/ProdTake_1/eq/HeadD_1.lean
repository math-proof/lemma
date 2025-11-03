import sympy.Basic


@[main, comm]
private lemma main
  [Monoid α]
-- given
  (s : List α) :
-- imply
  (s.take 1).prod = s.headD 1 := by
-- proof
  cases s <;>
    simp


-- created on 2025-07-15
