import Theorem.List.Cons.eq.Append
import Theorem.List.AppendAppend.eq.Append_Append
import Theorem.List.Append.of.Eq
import Theorem.List.LengthTake.eq.Min_Length
import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
import Theorem.Nat.Le_Min.is.Le.Le
import Theorem.List.TakeTake.eq.Take.of.Ge
import Theorem.List.Append.of.Eq.Eq
import Lemma.List.Take_1.eq.ListGet_0.of.GtLength_0
import Lemma.List.TailTake.eq.TakeTail
open List Nat


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0)
  (d : ℕ) :
-- imply
  s.permute ⟨0, h⟩ d = (s.take (d + 1)).rotate 1 ++ s.drop (d + 1) := by
-- proof
  unfold List.permute
  simp
  rw [Cons.eq.Append]
  rw [Append_Append.eq.AppendAppend]
  apply Append.of.Eq
  rw [Rotate.eq.AppendDrop__Take.of.GeLength]
  ·
    rw [TakeTake.eq.Take.of.Ge (by linarith)]
    apply Append.of.Eq.Eq
    ·
      unfold List.slice List.array_slice
      simp
      rw [TailTake.eq.TakeTail]
    ·
      apply Eq.symm
      apply Take_1.eq.ListGet_0.of.GtLength_0 h
  ·
    rw [LengthTake.eq.Min_Length]
    grind


-- created on 2025-06-17
-- updated on 2026-11-22
