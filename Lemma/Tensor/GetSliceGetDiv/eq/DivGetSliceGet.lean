import Lemma.Nat.CoeAdd_1.eq.AddCoe_1
import Lemma.Tensor.GetSliceDiv.eq.DivGetSlice
open Nat Tensor
set_option maxHeartbeats 600000


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GetSliceGetDiv.eq.DivGetSliceGet |
| fin | Tensor.GetSliceGetDiv.eq.DivGetSliceGet.fin |
-/
@[main, fin]
private lemma main
  [Div α]
-- given
  (X : Tensor α [n, m])
  (a : α)
  (i : Fin n) :
-- imply
  (X / a)[i][:i + 1] = X[i][:i + 1] / a := by
-- proof
  rw [AddCoe_1.eq.CoeAdd_1]
  simp [GetElem.getElem]
  rw [GetDiv.eq.DivGet.scalar.fin (X := X) (a := a) (i := i)]
  apply GetSliceDiv.eq.DivGetSlice


-- created on 2026-08-18
-- updated on 2026-08-19
