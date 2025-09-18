import stdlib.List
import Lemma.Algebra.SliceAppend.eq.Take_Sub_Length
open Algebra


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
