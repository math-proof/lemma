import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Vector.SEqRepeat_Div
import sympy.tensor.Basic
open Bool List Vector


@[main]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  X.unsqueeze d = ⟨cast (congrArg (List.Vector α) (Prod.eq.ProdInsertIdx s d)) X.data⟩ := by
-- proof
  unfold Tensor.unsqueeze Tensor.reshape
  simp
  apply EqCastS.of.SEq.Eq (by rw [Prod.eq.ProdInsertIdx])
  rw [ProdInsertIdx.eq.Prod]
  apply SEqRepeat_Div


-- created on 2026-07-10
