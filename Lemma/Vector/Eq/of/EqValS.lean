import Lemma.Bool.EqUFnS.of.Eq
import sympy.vector.Basic
open Bool


@[main]
private lemma main
  {a b : List.Vector α n}
-- given
  (h : a.val = b.val) :
-- imply
  a = b :=
-- proof
  List.Vector.eq a b h


@[main]
private lemma nat
  {a : List.Vector α n}
  {b : List.Vector α n'}
-- given
  (h : a.val = b.val) :
-- imply
  n = n' := by
-- proof
  have := EqUFnS.of.Eq h List.length
  simp at this
  assumption


-- created on 2025-10-03
