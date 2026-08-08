import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.EqData0'0
import Lemma.Vector.EqGet0_0
import sympy.tensor.tensor
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Le0Mul.is.Le0MulDataS |
| comm | Tensor.Le0MulDataS.is.Le0Mul |
| mp | Tensor.Le0MulDataS.of.Le0Mul |
| mpr | Tensor.Le0Mul.of.Le0MulDataS |
-/
@[main, comm, mp, mpr]
private lemma main
  [LE α] [Zero α] [Mul α]
  {A B : Tensor α s} :
-- imply
  A * B ≥ 0 ↔ A.data * B.data ≥ 0 := by
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
    conv_rhs => rw [DataMul.eq.MulDataS]
    rw [EqData0'0, EqGet0_0.fin]
    rwa [EqGet0_0.fin] at hi


-- created on 2026-08-08
