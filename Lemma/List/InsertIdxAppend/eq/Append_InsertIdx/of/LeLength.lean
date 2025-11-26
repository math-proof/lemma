import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx
import Lemma.Nat.EqAdd_Sub.of.Ge
open List Nat


@[main]
private lemma main
  {a : List α}
-- given
  (h : a.length ≤ i)
  (x : α) :
-- imply
  (a ++ b).insertIdx i x = a ++ b.insertIdx (i - a.length) x := by
-- proof
  have := InsertIdxAppend.eq.Append_InsertIdx a b (i - a.length) x
  rwa [EqAdd_Sub.of.Ge h] at this


-- created on 2025-06-09
