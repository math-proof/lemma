import Lemma.List.Cons.eq.Append
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.List.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.Algebra.Le_Min.of.Le.Le
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.List.EqAppendS.of.Eq.Eq
import Lemma.List.Take_1.eq.ListGet_0.of.GtLength_0
import Lemma.List.TakeTail.eq.TailTake
open Algebra List


@[main]
private lemma main
  {a : List α}
-- given
  (h : a.length > 0)
  (i : ℕ) :
-- imply
  a.permute ⟨0, h⟩ i = (a.take (i + 1)).rotate 1 ++ a.drop (i + 1) := by
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
      unfold List.slice List.array_slice Function.comp
      simp
      apply TakeTail.eq.TailTake
    ·
      apply Eq.symm
      apply Take_1.eq.ListGet_0.of.GtLength_0 h
  ·
    rw [LengthTake.eq.Min_Length]
    apply Le_Min.of.Le.Le
    ·
      simp_all
    ·
      linarith


-- created on 2025-06-17
