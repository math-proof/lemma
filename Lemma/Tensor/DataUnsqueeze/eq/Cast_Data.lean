import sympy.tensor.Basic
import Lemma.List.ProdInsertIdx.eq.Prod
open List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.unsqueeze d).data = cast (congrArg (List.Vector α) (Prod.eq.ProdInsertIdx s d)) X.data := by
-- proof
  simp [Tensor.unsqueeze]


-- created on 2025-11-30
