import Lemma.List.Prod.eq.Foldr
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.GetMap.eq.UFnGet
import sympy.tensor.tensor
open Tensor Vector List


@[main]
private lemma main
  {β : Type*}
-- given
  (X : Tensor α s)
  (f : α → β)
  (i : Fin X.length) :
-- imply
  (X.map f).get ⟨i, by grind⟩ = (X.get i).map f := by
-- proof
  match s with
  | [] =>
    have h_i := i.isLt
    unfold Tensor.length at h_i
    simp_all
  | n :: s =>
    unfold Tensor.map
    apply Eq.of.EqDataS
    simp
    repeat rw [DataGet.eq.GetUnflattenData.fin]
    simp
    ext j
    repeat erw [GetUnflatten.eq.Get_AddMul.fin]
    simp [Foldr.eq.Prod]
    erw [GetMap.eq.UFnGet]
    erw [GetMap.eq.UFnGet]
    congr 1
    exact (GetUnflatten.eq.Get_AddMul.fin (v := X.data) (i := ⟨i, by grind⟩) j).symm


-- created on 2025-12-23
