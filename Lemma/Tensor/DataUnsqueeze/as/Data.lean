import Lemma.Bool.SEqCast.of.Eq
import Def.Data.Tensor.Prod
import Lemma.Tensor.Unsqueeze.eq.TensorCast_Data
open Bool List Tensor


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.DataUnsqueeze.as.Data |
| cast | Tensor.DataUnsqueeze.eq.Cast_Data |
-/
@[path, cast]
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
  apply (ProdInsertIdx.eq.Prod s d).symm


-- created on 2025-11-30
-- updated on 2026-11-20
