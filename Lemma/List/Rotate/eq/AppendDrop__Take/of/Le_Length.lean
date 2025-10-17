import stdlib.List
import sympy.Basic


@[main]
private lemma main
  {v : List α}
  {n : ℕ}
-- given
  (h : n ≤ v.length) :
-- imply
  v.rotate n = v.drop n ++ v.take n := by
-- proof
  apply List.rotate_eq_drop_append_take h


-- created on 2025-06-17
-- updated on 2025-10-17
