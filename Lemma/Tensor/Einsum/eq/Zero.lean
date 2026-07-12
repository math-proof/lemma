import Lemma.Vector.Sum.eq.Zero
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Einsum.eq.SumMulDataS
open Tensor Vector


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X Y : Tensor α [0]) :
-- imply
  X.einsum Y = 0 := by
-- proof
  simp [Einsum.eq.SumMulDataS]
  apply Eq.of.EqDataS
  simp [Tensor.sum, EqData0'0]
  apply Eq.of.All_EqGetS
  intro i
  simp [Sum.eq.Zero]
  rfl


-- created on 2026-07-06
