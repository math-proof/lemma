import stdlib.List
import sympy.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h : start ≥ stop) :
-- imply
  a.slice start stop = .nil := by
-- proof
  unfold List.slice List.array_slice
  simp_all


-- created on 2025-06-07
