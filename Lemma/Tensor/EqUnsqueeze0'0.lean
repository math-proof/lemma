import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Unsqueeze.eq.TensorCast_Data
import Lemma.Vector.EqCast_0'0.of.Eq
open List Tensor Vector


@[main]
private lemma main
  [Zero α]
-- given
  (s : List ℕ)
  (d : ℕ) :
-- imply
  (0 : Tensor α s).unsqueeze d = 0 := by
-- proof
  rw [Unsqueeze.eq.TensorCast_Data]
  apply Eq.of.EqDataS
  simp [EqData0'0]
  apply EqCast_0'0.of.Eq
  rw [ProdInsertIdx.eq.Prod]


-- created on 2026-07-14
