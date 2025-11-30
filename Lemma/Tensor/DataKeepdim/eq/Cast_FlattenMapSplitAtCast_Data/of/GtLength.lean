import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataKeepdim.as.FlattenMapSplitAtCast_Data.of.GtLength
open Bool List Nat Tensor


@[main]
private lemma main
  {d : ℕ}
  {s : List ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α (s.eraseIdx d)) :
-- imply
  have h_prod : (((s.eraseIdx d).insertIdx d 1).take d).prod * (s[d] * (((s.eraseIdx d).insertIdx d 1).drop d).prod) = s.prod := by
    simp [Mul_Mul.eq.MulMul.comm]
    apply MulProdInsertIdxEraseIdx.eq.Prod.of.GtLength
  X.keepdim.data = cast
    (by rw [h_prod])
    ((((cast (congrArg (List.Vector α) (Prod.eq.ProdInsertIdx (s.eraseIdx d) d)) X.data).splitAt d).map (·.repeat s[d])).flatten) := by
-- proof
  intro h_prod
  apply Eq_Cast.of.SEq.Eq h_prod
  apply DataKeepdim.as.FlattenMapSplitAtCast_Data.of.GtLength


-- created on 2025-11-30
