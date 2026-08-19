import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.GetAppend.eq.AppendGetS
import Lemma.Tensor.GetAppend.eq.Get
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
open Bool Tensor


@[main, fin]
private lemma main
-- given
  (h : i < n)
  (A : Tensor α (n :: s))
  (B : Tensor α (m :: s)) :
-- imply
  have : i < n + m := by linarith
  (A ++ B)[i] = A[i] := by
-- proof
  let i : Fin n := ⟨i, h⟩
  have := GetAppend.eq.Get A B i
  simp_all
  assumption


@[main]
private lemma batch
-- given
  (h : j < n)
  (A : Tensor α ([d] ++ n :: s))
  (B : Tensor α ([d] ++ m :: s))
  (i : Fin d) :
-- imply
  have : j < n + m := Nat.lt_add_right m h
  (A ++ B)[i, j] = A[i][j] := by
-- proof
  apply Eq.of.SEq
  apply (SEqGetS.of.SEq.GtLength (i := j) (by grind) (SEq.of.Eq (GetAppend.eq.AppendGetS A B i))).trans
  apply SEq.of.Eq
  apply main h


-- created on 2025-06-01
-- updated on 2026-08-19
