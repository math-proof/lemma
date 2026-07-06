import Lemma.Vector.Sum.eq.Zero
import Lemma.Fin.Eq_0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Matmul.eq.SumMulDataS
open Fin Tensor Vector


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X Y : Tensor α [0]) :
-- imply
  X.matmul Y = 0 := by
-- proof
  simp [Matmul.eq.SumMulDataS]
  apply Eq.of.EqDataS
  simp
  rw [EqData0'0]
  ext t
  have h_t := Eq_0 t
  subst h_t
  rw [EqGet0_0.fin]
  simp [List.Vector.get]
  apply Sum.eq.Zero


-- created on 2026-07-06
