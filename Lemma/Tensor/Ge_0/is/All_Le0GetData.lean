import Lemma.Tensor.EqData0'0
import Lemma.Vector.EqGet0_0
import Lemma.Vector.Le.is.All_Le
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Ge_0.is.All_Le0GetData |
| comm | Tensor.All_Le0GetData.is.Ge_0 |
| mp | Tensor.All_Le0GetData.of.Ge_0 |
| mpr | Tensor.Ge_0.of.All_Le0GetData |
-/
@[main, comm, mp, mpr]
private lemma main
  [LE α] [Zero α]
  {A : Tensor α s} :
-- imply
  A ≥ 0 ↔ ∀ k : Fin s.prod, A.data[k] ≥ 0 := by
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
    rw [ge_iff_le]
    simp only [LE.le]
    rw [EqData0'0]
    apply Vector.Le.of.All_Le
    intro i
    have hi := h i
    dsimp [GetElem.getElem] at hi ⊢
    rwa [EqGet0_0.fin (α := α)]


-- created on 2026-07-27
