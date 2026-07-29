import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Vector.MapExp.eq.ExpMap.of.All_EqUFnExp_ExpUFn
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.MapExp.eq.ExpMap.of.All_EqUFnExp_ExpUFn |
| comm | Tensor.ExpMap.eq.MapExp.of.All_EqUFnExp_ExpUFn |
-/
@[main, comm]
private lemma main
  [Exp α]
  [Exp β]
  {f : α → β}
-- given
  (hf : ∀ x, f (exp x) = exp (f x))
  (X : Tensor α s) :
-- imply
  (exp X).map f = exp (X.map f) := by
-- proof
  apply Eq.of.EqDataS
  simp [Tensor.map]
  rw [DataExp.eq.ExpData]
  apply MapExp.eq.ExpMap.of.All_EqUFnExp_ExpUFn hf


-- created on 2026-07-28
