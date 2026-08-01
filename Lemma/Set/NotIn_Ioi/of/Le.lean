import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x a : α}
-- given
  (h : x ≤ a) :
-- imply
  x ∉ Ioi a := by
-- proof
  contrapose! h
  assumption


-- created on 2019-02-07
