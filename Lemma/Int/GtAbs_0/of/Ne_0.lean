import Lemma.Int.NeAbs_0.of.Ne_0
import Lemma.Algebra.GeAbs_0
import Lemma.Algebra.Gt.is.Ge.Ne
open Algebra Int


@[main]
private lemma main
  [AddGroup α] [LinearOrder α] [AddLeftMono α] [AddRightMono α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  |a| > 0 := by
-- proof
  have h_Ne := NeAbs_0.of.Ne_0 h
  have h_Ge := GeAbs_0 (a := a)
  apply Gt.of.Ge.Ne h_Ge h_Ne


-- created on 2025-04-20
