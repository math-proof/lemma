import Lemma.List.Prod.eq.Foldr
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
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
    simp
    repeat rw [GetUnflatten.eq.Get_AddMul.fin]
    simp [Foldr.eq.Prod]


-- created on 2025-12-23
