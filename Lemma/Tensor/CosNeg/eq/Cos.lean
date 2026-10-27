import Lemma.Tensor.DataCos.eq.CosData
import Lemma.Vector.CosNeg.eq.Cos
import Theorem.Data.Holor.Functions
open Tensor Vector


@[path]
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
