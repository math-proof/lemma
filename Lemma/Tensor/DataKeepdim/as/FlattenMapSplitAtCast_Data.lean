import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqSetInsertIdxEraseIdx.of.GtLength
import Lemma.List.MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataRepeat.eq.Cast_FlattenMapSplitAtData
import Lemma.Tensor.DataUnsqueeze.eq.Cast_Data
import Lemma.Tensor.Keepdim.as.RepeatUnsqueeze
import Lemma.Tensor.SEqDataS.of.SEq
open Bool List Nat Tensor


@[main]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (X : Tensor α (s.eraseIdx d)) :
-- imply
  X.keepdim.data ≃ (((cast (congrArg (List.Vector α) (Prod.eq.ProdInsertIdx (s.eraseIdx d) d)) X.data).splitAt d).map (·.repeat s[d])).flatten := by
-- proof
  have := Keepdim.as.RepeatUnsqueeze X
  have := SEqDataS.of.SEq this
  apply this.trans
  simp [DataRepeat.eq.Cast_FlattenMapSplitAtData]
  apply SEqCast.of.SEq.Eq
  ·
    simp [Mul_Mul.eq.MulMul.comm]
    simp [EqSetInsertIdxEraseIdx.of.GtLength]
    apply MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength
  ·
    rw [DataUnsqueeze.eq.Cast_Data]


-- created on 2025-11-29
-- updated on 2025-11-30
