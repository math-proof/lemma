import Lemma.Algebra.EqAppendTake__Drop
import Lemma.Algebra.EqAddSub.of.Ge
import Lemma.Algebra.TakeTail.eq.TailTake
open Algebra


@[main]
private lemma main
  
  {d : ℕ}
-- given
  (h : d > 0) 
  (s : List α):
-- imply
  s.tail = (s.take d).tail ++ s.drop d := by
-- proof
  rw [← EqAppendTake__Drop s.tail (d - 1)]
  simp
  rw [EqAddSub.of.Ge (by assumption)]
  congr
  rw [TakeTail.eq.TailTake]
  rwa [EqAddSub.of.Ge]


-- created on 2025-07-06
