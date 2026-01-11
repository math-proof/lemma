import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.EqAppendTake__Drop
import Lemma.List.ZipWith__Append.eq.AppendZipWithS
import Lemma.Tensor.BroadcastMatmul.as.BroadcastMatmulRec.of.GtLengthS
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength
import sympy.tensor.tensor
open Tensor Bool List


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h : s.length > s'.length)
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α (s' ++ [n, k]))
  (i : Fin s[0]) :
-- imply
  let Xi : Tensor α (s.tail ++ [m, n]) := cast (by grind) (X[i]'(GtLength.of.GtLength (by simpa) X ⟨i, by grind⟩ (j := s'.length + 2)))
  (X.broadcast_matmul Y)[i]'(GtLength.of.GtLength (by simp [broadcast_shape]; grind) (X.broadcast_matmul Y) ⟨i, by simp [broadcast_shape]; grind⟩ (j := s'.length + 2)) ≃ Xi.broadcast_matmul_rec (Y.broadcast (s.tail.take (s.tail.length - s'.length) ++ s' ++ [n, k]) (by simp)) (by grind) := by
-- proof
  simp only [GetElem.getElem]
  have := BroadcastMatmul.as.BroadcastMatmulRec.of.GtLengthS h X Y
  have := Eq_Cast.of.SEq this
  rw [this]
  rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by simp [broadcast_shape]; grind⟩)]
  ·
    simp
    apply SEqCast.of.SEq.Eq
    ·
      simp [broadcast_shape]
      split_ifs
      repeat omega
      simp
      rw [Append_Append.eq.AppendAppend]
      congr
      rw [ZipWith__Append.eq.AppendZipWithS]
      apply EqAppendS.of.Eq
      simp
    ·
      conv_lhs => unfold broadcast_matmul_rec
      sorry
  ·
    simp [broadcast_shape]
    split_ifs
    repeat omega
    simp
    rw [Append_Append.eq.AppendAppend]
    apply EqAppendS.of.Eq
    rw [ZipWith__Append.eq.AppendZipWithS]
    apply EqAppendS.of.Eq
    simp
  ·
    simp [broadcast_shape]


-- created on 2026-01-11
