module

public import Theorem.List.EqAppendTake__Drop

public section

open List


public theorem List.AppendFlattenS.eq.Flatten
-- given
  (s : List (List α))
  (n : ℕ) :
-- imply
  (s.take n).flatten ++ (s.drop n).flatten = s.flatten := by
-- proof
  rw [← EqAppendTake__Drop s n, List.flatten_append]
  simp


-- created on 2025-06-14
