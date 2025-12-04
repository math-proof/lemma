import Lemma.Real.NeExp_0
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.Div.eq.One.of.All_Ne_0
import Lemma.Tensor.EqKeepdimCast.of.LeLength
import Lemma.Tensor.Softmax.eq.Div_SumExp
import Lemma.Tensor.Sum.eq.Cast_Sum.of.LeLength
import Lemma.Vector.GetExp.eq.ExpGet
open Tensor Vector


@[main, comm]
private lemma main
  [ExpRing α]
  {d : ℕ}
-- given
  (h : s.length ≤ d)
  (X : Tensor α s) :
-- imply
  X.softmax d = 1 := by
-- proof
  rw [Softmax.eq.Div_SumExp]
  rw [Sum.eq.Cast_Sum.of.LeLength h]
  rw [EqKeepdimCast.of.LeLength h]
  apply @Tensor.Div.eq.One.of.All_Ne_0
  intro i
  rw [DataExp.eq.ExpData]
  rw [GetExp.eq.ExpGet]
  apply Real.NeExp_0


-- created on 2025-11-28
