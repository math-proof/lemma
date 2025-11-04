import Lemma.List.Cons.eq.Append
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.List.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.Nat.Le_Min.of.Le.Le
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.List.EqAppendS.of.Eq.Eq
import Lemma.List.Take_1.eq.ListGet_0.of.GtLength_0
import Lemma.List.TailTake.eq.TakeTail
open List Nat


@[main]
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
  apply EqAppendS.of.Eq
  rw [Rotate.eq.AppendDrop__Take.of.Le_Length]
  ·
    rw [TakeTake.eq.Take.of.Ge (by linarith)]
    apply EqAppendS.of.Eq.Eq
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
