import stdlib.List
import sympy.Basic


@[main, comm]
private lemma main
  {s : List α}
  {n : ℕ}
-- given
  (h : s.length ≥ n) :
-- imply
  s.rotate n = s.drop n ++ s.take n := by
-- proof
  apply List.rotate_eq_drop_append_take h


-- created on 2025-06-17
-- updated on 2025-10-17
