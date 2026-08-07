import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData1'1
import Lemma.Vector.EqGet1_1
import sympy.sets.fancysets
open Tensor Vector


@[main, comm]
private lemma main
-- given
  (s : List ℕ) :
-- imply
  (1 : Tensor ℝ* s) = (1 : Tensor ℝ s) := by
-- proof
  apply Eq.of.EqDataS
  simp [Tensor.map]
  simp [EqData1'1]
  ext i
  simp [EqGet1_1.fin]


-- created on 2026-07-29
