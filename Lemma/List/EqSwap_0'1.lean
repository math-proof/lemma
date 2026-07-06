import stdlib.List
import sympy.Basic


@[main]
private lemma main
-- given
  (a b : α)
  (c : List α := []) :
-- imply
  (a :: b :: c).swap 0 1 = b :: a :: c := by
-- proof
  simp [List.swap, List.slice, List.array_slice]


-- created on 2025-06-16
