module

public import Theorem.List.Drop.eq.Cons_Drop_Add_1.of.GtLength

public section

open List


public theorem List.FlattenDrop.eq.Append_FlattenDrop.of.GtLength
  {i : ℕ}
  {s : List (List α)}
-- given
  (h : s.length > i) :
-- imply
  (s.drop i).flatten = s[i] ++ (s.drop (i + 1)).flatten := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength h]
  simp [List.flatten]


-- created on 2025-06-14
