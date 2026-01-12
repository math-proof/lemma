import Lemma.Tensor.GetBroadcastMatmul.as.BroadcastMatmulRecGet.of.GtLengthS
import Lemma.Tensor.GtLength.of.GtLength
import Lemma.Tensor.SEqBroadcastMatmulRecS.of.SEq.SEq
import Lemma.Tensor.SEqBroadcastS.of.Eq.Eq
open Tensor


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α [n, k])
  (i : Fin s[0]) :
-- imply
  have h_s : [n, k] = [] ++ [n, k] := by simp
  let Y := cast (congrArg (Tensor α) h_s) Y
  let Xi : Tensor α (s.tail ++ [m, n]) := cast (by grind) (X[i]'(GtLength.of.GtLength (by simpa) X ⟨i, by grind⟩ (j := 2)))
  (X.broadcast_matmul Y)[i]'(GtLength.of.GtLength (by simp [broadcast_shape]; grind) (X.broadcast_matmul Y) ⟨i, by simp [broadcast_shape]; grind⟩ (j := 2)) ≃ Xi.broadcast_matmul_rec (Y.broadcast (s.tail ++ [n, k]) (by simp)) (by grind) := by
-- proof
  intro h_s Y Xi
  simp [Xi]
  simp only [GetElem.getElem]
  have := GetBroadcastMatmul.as.BroadcastMatmulRecGet.of.GtLengthS.fin (by grind) X Y i
  simp at this
  apply this.trans
  apply SEqBroadcastMatmulRecS.of.SEq.SEq
  ·
    simp
  ·
    rfl
  ·
    apply SEqBroadcastS.of.Eq.Eq
    ·
      simp
    ·
      rfl


-- created on 2026-01-12
