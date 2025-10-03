import sympy.vector.Basic
import sympy.Basic


@[main]
private lemma main
  {a b : List.Vector α n}
-- given
  (h : a.val = b.val) :
-- imply
  a = b :=
-- proof
  List.Vector.eq a b h


-- created on 2025-10-03
