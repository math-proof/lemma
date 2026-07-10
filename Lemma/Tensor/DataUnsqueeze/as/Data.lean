import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Tensor.Unsqueeze.eq.TensorCast_Data
open Bool List Tensor


@[main, cast]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.unsqueeze d).data ≃ X.data := by
-- proof
  rw [Unsqueeze.eq.TensorCast_Data]
  apply SEqCast.of.Eq
  apply Prod.eq.ProdInsertIdx


-- created on 2025-11-30
-- updated on 2026-07-10
