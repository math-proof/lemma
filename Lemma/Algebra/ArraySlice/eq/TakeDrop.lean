import stdlib.List
import sympy.Basic


@[main, comm]
private lemma main
-- given
  (v : List α) :
-- imply
  v.array_slice i d = (v.drop i).take d := by
-- proof
  simp [List.array_slice]


-- created on 2025-05-08
