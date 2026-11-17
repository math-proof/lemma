module

public import Theorem.List.LengthMap.eq.Length

public section

open List


public theorem List.EqMapMap
-- given
  (s : List ℕ) :
-- imply
  (s.map List.range).map List.length = s := by
-- proof
  ext i k
  simp_all


-- created on 2025-06-11
