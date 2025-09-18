import Lemma.Algebra.Cons.eq.Append
import Lemma.Algebra.AppendAppend.eq.Append_Append
import Lemma.Algebra.EqAppendS.of.Eq
import Lemma.Algebra.LengthTake.eq.Min_Length
import Lemma.Algebra.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.Algebra.Le_Min.of.Le.Le
import Lemma.Algebra.TakeTake.eq.Take.of.Ge
import Lemma.Algebra.EqAppendS.of.Eq.Eq
import Lemma.Algebra.Take_1.eq.List.of.Gt_0
import Lemma.Algebra.TakeTail.eq.TailTake
open Algebra


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
      apply Take_1.eq.List.of.Gt_0 h
  ·
    rw [LengthTake.eq.Min_Length]
    apply Le_Min.of.Le.Le
    ·
      simp_all
    ·
      linarith


-- created on 2025-06-17
