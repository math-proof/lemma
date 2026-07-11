import Lemma.List.InsertIdxAppend.eq.Append_Cons
open List Nat


@[main]
private lemma main
-- given
  (s : List α)
  (x : α) :
-- imply
  s.insertIdx s.length x = s ++ [x] := by
-- proof
  have := InsertIdxAppend.eq.Append_Cons s [] x
  simp_all


-- created on 2026-07-11
