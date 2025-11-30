import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Tensor.DataUnsqueeze.as.Data
open Bool List Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.unsqueeze d).data = cast (congrArg (List.Vector α) (Prod.eq.ProdInsertIdx s d)) X.data := by
-- proof
  apply Eq_Cast.of.SEq.Eq
  ·
    apply Prod.eq.ProdInsertIdx
  ·
    apply DataUnsqueeze.as.Data


-- created on 2025-11-30
