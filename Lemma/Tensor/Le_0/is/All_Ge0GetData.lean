import Lemma.Tensor.EqData0'0
import Lemma.Vector.EqGet0_0
import Lemma.Vector.Le.is.All_Le
import sympy.tensor.tensor
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Le_0.is.All_Ge0GetData |
| comm | Tensor.All_Ge0GetData.is.Le_0 |
| mp | Tensor.All_Ge0GetData.of.Le_0 |
| mpr | Tensor.Le_0.of.All_Ge0GetData |
-/
@[main, comm, mp, mpr]
private lemma main
  [LE α] [Zero α]
  {A : Tensor α s} :
-- imply
  A ≤ 0 ↔ ∀ k : Fin s.prod, A.data[k] ≤ 0 := by
-- proof
  constructor
  ·
    intro h k
    have h' := h k
    dsimp [LE.le, GetElem.getElem] at h'
    rw [EqData0'0] at h'
    rwa [EqGet0_0.fin] at h'
  ·
    intro h
    dsimp [LE.le]
    rw [EqData0'0]
    apply Vector.Le.of.All_Le
    intro i
    have hi := h i
    dsimp [GetElem.getElem] at hi ⊢
    rw [EqGet0_0.fin (α := α)]
    exact hi


-- created on 2026-07-27
