import Lemma.Set.Icc.eq.Empty.of.Gt
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  Icc y x = ∅ :=
-- proof
  Set.Icc.eq.Empty.of.Gt h


-- created on 2019-09-22
