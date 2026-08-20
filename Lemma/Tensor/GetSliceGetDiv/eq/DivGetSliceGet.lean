import Lemma.Tensor.GetSliceDiv.eq.DivGetSlice
open Tensor
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
  (i : Fin n)
  (j k : ℕ) :
-- imply
  (X / a)[i][j:k] = X[i][j:k] / a := by
-- proof
  simp [GetElem.getElem]
  rw [GetDiv.eq.DivGet.scalar.fin (X := X) (a := a) (i := i)]
  apply GetSliceDiv.eq.DivGetSlice


-- created on 2026-08-18
-- updated on 2026-08-20
