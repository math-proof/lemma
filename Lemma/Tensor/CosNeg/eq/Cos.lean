import Lemma.Tensor.DataCos.eq.CosData
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.CosNeg.eq.Cos
import sympy.tensor.functions
open Tensor Vector


@[main]
private lemma main
-- given
  (X : Tensor ℝ s) :
-- imply
  (-X).cos = X.cos := by
-- proof
  apply Eq.of.EqDataS
  simp [DataCos.eq.CosData, DataNeg.eq.NegData]
  exact CosNeg.eq.Cos X.data


-- created on 2026-09-03
