import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.Tensor.BroadcastMatmulRec.as.FromVectorMap₂_CastS_ToVector.of.EqGetS_0.EqLengthS.GtLength_0
import Lemma.Tensor.GetFromVector.eq.Get
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEqBroadcastMatmulRecS.of.SEq.SEq
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Vector.GetCast.eq.Get.of.Eq
import sympy.tensor.tensor
open Bool List Tensor Vector


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h : s.length > 0)
  (h_length : s.length = s'.length)
  (h_0 : s[0] = s'[0])
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α (s' ++ [n, k]))
  (i : Fin s[0]) :
-- imply
  let Xi : Tensor α (s.tail ++ [m, n]) := cast
    (by rw [TailAppend.eq.AppendTail.of.GtLength_0 (by grind)])
    (X.get ⟨i, GtLength.of.GtLength_0 (by grind) X ⟨i, by grind⟩⟩)
  let Yi : Tensor α (s'.tail ++ [n, k]) := cast
    (by rw [TailAppend.eq.AppendTail.of.GtLength_0 (by grind)])
    (Y.get ⟨i, GtLength.of.GtLength_0 (by grind) Y ⟨i, by grind⟩⟩)
  have h_i : i < (X.broadcast_matmul_rec Y h_length).length := by
    rw [Length.eq.Get_0.of.GtLength_0 (by grind)]
    simp [broadcast_shape]
    grind
  (X.broadcast_matmul_rec Y (by grind)).get ⟨i, h_i⟩ ≃ Xi.broadcast_matmul_rec Yi (by simp; grind) := by
-- proof
  intro Xi Yi h_i
  have := BroadcastMatmulRec.as.FromVectorMap₂_CastS_ToVector.of.EqGetS_0.EqLengthS.GtLength_0 h h_length h_0 X Y
  simp at this
  have := SEqGetS.of.SEq.GtLength.fin h_i this (i := i)
  simp at this
  apply this.trans
  simp [GetFromVector.eq.Get.fin]
  simp [Xi, Yi]
  apply SEqBroadcastMatmulRecS.of.SEq.SEq
  ·
    grind
  repeat {
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      grind
    ·
      grind
    ·
      rw [GetCast.eq.Get.of.Eq.fin]
      ·
        simp [Tensor.get]
        simp only [GetElem.getElem]
        rfl
      ·
        rw [HeadD.eq.Get_0.of.GtLength_0 (by grind)]
        grind
  }


-- created on 2026-01-11
