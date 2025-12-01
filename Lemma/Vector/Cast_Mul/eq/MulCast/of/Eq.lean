import sympy.Basic
import sympy.vector.vector


@[main]
private lemma main
  [Mul α]
-- given
  (h : n = n')
  (x : List.Vector α n)
  (a : α) :
-- imply
  have h := congrArg (List.Vector α) h
  cast h (x * a) = cast h x * a := by
-- proof
  sorry


-- created on 2025-12-01
