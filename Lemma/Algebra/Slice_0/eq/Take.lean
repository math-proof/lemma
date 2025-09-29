import stdlib.List
import sympy.Basic


@[main]
private lemma main
-- given
  (a : List α) :
-- imply
  a.slice 0 n = a.take n := by
-- proof
  unfold List.slice List.array_slice Function.comp
  simp


-- created on 2025-06-18
