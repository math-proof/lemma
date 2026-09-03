import Lemma.Tensor.DataCos.eq.CosData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.EqData1'1
import Lemma.Vector.Cos0.eq.One
open Tensor


@[main]
private lemma main
  {s : List ℕ} :
-- imply
  (0 : Tensor ℝ s).cos = 1 := by
-- proof
  apply Eq.of.EqDataS
  rw [DataCos.eq.CosData, EqData0'0, EqData1'1]
  exact Vector.Cos0.eq.One


-- created on 2026-09-03
