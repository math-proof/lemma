import stdlib.SEq
import sympy.Basic


@[main, comm 2]
private lemma main
  {Vector : α → Sort v}
  {a b : Vector n}
-- given
  (h : n = m)
  (h_eq : a = b) :
-- imply
  cast (congrArg Vector h) a ≃ b := by
-- proof
  aesop


-- created on 2025-10-06
