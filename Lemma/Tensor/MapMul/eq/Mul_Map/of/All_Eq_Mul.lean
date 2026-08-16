import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Eq.is.All_EqGetS
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.MapMul.eq.Mul_Map.of.All_Eq_Mul |
| comm | Tensor.Mul_Map.eq.MapMul.of.All_Eq_Mul |
-/
@[main, comm]
private lemma main
  [Mul α] [Mul β]
  {f : α → β}
-- given
  (hf : ∀ a b, f (a * b) = f a * f b)
  (a : α)
  (A : Tensor α s) :
-- imply
  (a * A).map f = f a * A.map f := by
-- proof
  apply Eq.of.EqDataS
  apply Eq.of.All_EqGetS.fin
  intro i
  simp [Tensor.map, HMul.hMul]
  apply hf


-- created on 2026-08-17
