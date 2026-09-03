import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.DataSin.eq.SinData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.SinNeg.eq.NegSin
import sympy.tensor.functions
open Tensor Vector


@[main]
private lemma main
-- given
  (X : Tensor ℝ s) :
-- imply
  (-X).sin = -X.sin := by
-- proof
  apply Eq.of.EqDataS
  simp [DataSin.eq.SinData, DataNeg.eq.NegData]
  exact SinNeg.eq.NegSin X.data


-- created on 2026-09-03
