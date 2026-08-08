import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.EqData0'0
import Lemma.Vector.EqGet0_0
import sympy.tensor.tensor
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Ge0Mul.is.Ge0MulDataS |
| comm | Tensor.Ge0MulDataS.is.Ge0Mul |
| mp | Tensor.Ge0MulDataS.of.Ge0Mul |
| mpr | Tensor.Ge0Mul.of.Ge0MulDataS |
-/
@[main, comm, mp, mpr]
private lemma main
  [LE α] [Zero α] [Mul α]
  {A B : Tensor α s} :
-- imply
  A * B ≤ 0 ↔ A.data * B.data ≤ 0 := by
-- proof
  constructor
  · intro h i
    have hi := h i
    dsimp [GetElem.getElem] at hi ⊢
    rw [DataMul.eq.MulDataS] at hi
    exact hi
  · intro h i
    have hi := h i
    dsimp [GetElem.getElem] at hi ⊢
    conv_lhs => rw [DataMul.eq.MulDataS]
    rw [EqData0'0, EqGet0_0.fin]
    rwa [EqGet0_0.fin] at hi


-- created on 2026-08-08
