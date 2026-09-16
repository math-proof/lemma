import Lemma.Bool.Cast.of.SEq.Eq
import torch.Tensor.prod
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Vector.SEqRepeat_Div
import torch.Tensor.Basic
import torch.Tensor.reshape
import torch.Tensor.unsqueeze
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
  apply Cast.of.SEq.Eq (by rw [Prod.eq.ProdInsertIdx])
  rw [ProdInsertIdx.eq.Prod]
  apply SEqRepeat_Div


-- created on 2026-07-10
