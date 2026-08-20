import Lemma.Tensor.GetDiv.eq.DivGet
import Lemma.Tensor.GetGetSlice.eq.Get_Add.of.GtSubMin
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GetSliceDiv.eq.DivGetSlice |
| fin | Tensor.GetSliceDiv.eq.DivGetSlice.fin |
-/
@[main, fin]
private lemma main
  [Div α]
-- given
  (X : Tensor α (m :: s))
  (a : α)
  (j n : ℕ) :
-- imply
  (X / a)[j:n] = X[j:n] / a := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro t
  have h_t := t.isLt
  simp [Tensor.length, List.LengthSlice.eq.SubMin] at h_t
  apply (GetGetSlice.eq.Get_Add.of.GtSubMin.fin h_t (X / a)).trans
  apply (GetDiv.eq.DivGet.scalar.fin (X := X) (a := a) (i := ⟨j + t, by grind⟩)).trans
  apply Eq.symm
  apply (GetDiv.eq.DivGet.scalar.fin (X := X[j:n]) (a := a) (i := t)).trans
  apply congrArg (α := Tensor α s) (fun x => x / a)
  apply GetGetSlice.eq.Get_Add.of.GtSubMin.fin h_t X


-- created on 2026-08-18
-- updated on 2026-08-20
