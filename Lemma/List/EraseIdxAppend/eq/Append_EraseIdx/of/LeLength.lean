import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx
import Lemma.Nat.EqAdd_Sub.of.Ge
open List Nat


@[main]
private lemma main
  {a : List α}
-- given
  (h : a.length ≤ i)
  (b : List α) :
-- imply
  (a ++ b).eraseIdx i = a ++ b.eraseIdx (i - a.length) := by
-- proof
  have := EraseIdxAppend.eq.Append_EraseIdx a b (i - a.length)
  rwa [EqAdd_Sub.of.Ge (by omega)] at this


-- created on 2025-10-31
