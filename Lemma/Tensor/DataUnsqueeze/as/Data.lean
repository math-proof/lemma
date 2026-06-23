import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.ProdInsertIdx.eq.Prod
import sympy.tensor.Basic
open Bool List


@[main, cast]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.unsqueeze d).data ≃ X.data := by
-- proof
  simp [Tensor.unsqueeze]
  apply SEqCast.of.Eq
  apply Prod.eq.ProdInsertIdx


-- created on 2025-11-30
