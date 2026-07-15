import sympy.Basic
import sympy.vector.Basic


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (a b : List.Vector α n) :
-- imply
  a @ b = (a * b).sum  := by
-- proof
  rfl


-- created on 2026-07-15
