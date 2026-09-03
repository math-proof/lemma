import Lemma.Tensor.DataSin.eq.SinData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Vector.Sin0.eq.Zero
open Tensor


@[main]
private lemma main
  {s : List ℕ} :
-- imply
  (0 : Tensor ℝ s).sin = 0 := by
-- proof
  apply Eq.of.EqDataS
  rw [DataSin.eq.SinData, EqData0'0]
  exact Vector.Sin0.eq.Zero


-- created on 2026-09-03
