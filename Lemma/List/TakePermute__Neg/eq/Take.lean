import Lemma.List.EqTakeAppend.of.Eq_Length
import Lemma.List.TakePermute__Neg.eq.Append_RotateDropTake
import Lemma.List.TakeTake.eq.Take.of.Ge
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  (s.permute i (-d)).take (i - d) = s.take (i - d) := by
-- proof
  have := TakePermute__Neg.eq.Append_RotateDropTake i d
  have := congrArg (·.take (i - d)) this
  simp at this
  rw [TakeTake.eq.Take.of.Ge (by omega)] at this
  rw [this]
  rw [EqTakeAppend.of.Eq_Length]
  simp
  omega


-- created on 2025-10-27
