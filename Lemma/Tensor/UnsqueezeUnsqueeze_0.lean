import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.DataUnsqueeze.as.Data
import Lemma.Tensor.Eq.is.EqDataS
import sympy.tensor.tensor
open Bool Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α s) :
-- imply
  (X.unsqueeze 0).unsqueeze 1 = (X.unsqueeze 0).unsqueeze 0 := by
-- proof
  apply Eq.of.EqDataS
  apply Eq.of.SEq
  exact (DataUnsqueeze.as.Data (X := X.unsqueeze 0) (d := 1)).trans (DataUnsqueeze.as.Data (X := X.unsqueeze 0) (d := 0)).symm


-- created on 2026-07-30
