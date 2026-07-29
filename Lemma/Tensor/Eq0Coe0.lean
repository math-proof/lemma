import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Vector.EqGet0_0
import sympy.sets.fancyset
open Tensor Vector


@[main, comm]
private lemma main
-- given
  (s : List ℕ) :
-- imply
  (0 : Tensor ℝ* s) = (0 : Tensor ℝ s) := by
-- proof
  apply Eq.of.EqDataS
  simp [Tensor.map]
  simp [EqData0'0]
  ext i
  simp [EqGet0_0.fin]


-- created on 2026-07-29
