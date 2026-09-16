import Lemma.Bool.Cast.of.SEq.Eq
import torch.Tensor.prod
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Vector.SEqRepeat_Div
import torch.Tensor.Basic
import torch.Tensor.reshape
import torch.Tensor.unsqueeze
open Bool List Vector


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  X.unsqueeze d = X.reshape (s.insertIdx d 1) (by simp [Prod.eq.ProdInsertIdx s d]) := by
-- proof
  simp [Tensor.unsqueeze]


-- created on 2026-07-12
