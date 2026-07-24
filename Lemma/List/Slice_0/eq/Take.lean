import stdlib.List
import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α) :
-- imply
  s.slice 0 n = s.take n := by
-- proof
  unfold List.slice List.array_slice Function.comp
  simp


-- created on 2025-06-18
