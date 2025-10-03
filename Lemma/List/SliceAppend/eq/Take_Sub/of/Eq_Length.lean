import stdlib.List
import Lemma.List.SliceAppend.eq.Take_Sub_Length
open List


@[main]
private lemma main
  {a : List α}
-- given
  (h : a.length = i)
  (b : List α)
  (j : ℕ) :
-- imply
  (a ++ b).slice i j = b.take (j - i) := by
-- proof
  rw [← h]
  apply SliceAppend.eq.Take_Sub_Length


-- created on 2025-05-18
