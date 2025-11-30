import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Tensor.DataUnsqueeze.eq.Cast_Data
open Bool Tensor List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.unsqueeze d).data ≃ X.data := by
-- proof
  rw [DataUnsqueeze.eq.Cast_Data]
  apply SEqCast.of.Eq
  apply Prod.eq.ProdInsertIdx


-- created on 2025-11-30
