import Lemma.Rat.DivMulS.eq.Div.of.Ne_0
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Vector.ExpAdd.eq.MulExpS
import Lemma.Vector.Softmax.eq.Div_SumExp
import Lemma.Vector.SumMul.eq.MulSum
import sympy.tensor.functions
open Rat Vector


@[main]
private lemma main
  [ExpRing α]
-- given
  (x : List.Vector α n)
  (δ : α) :
-- imply
  (x + δ).softmax = x.softmax := by
-- proof
  simp [Softmax.eq.Div_SumExp]
  rw [ExpAdd.eq.MulExpS.scalar]
  rw [SumMul.eq.MulSum]
  ext i
  repeat rw [GetDiv.eq.DivGet.fin]
  rw [GetMul.eq.MulGet.fin]
  rw [DivMulS.eq.Div.of.Ne_0]
  apply ExpNeZero.exp_ne_zero


-- created on 2025-11-30
