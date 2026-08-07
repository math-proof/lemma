import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.GetTranspose.eq.Get
open Tensor


@[main]
private lemma main
  {f : α → β}
-- given
  (X : Tensor α [n, m]) :
-- imply
  (X.map f)ᵀ = Xᵀ.map f := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_lhs => erw [GetTranspose.eq.Get.fin]
  conv_lhs => erw [GetMap.eq.MapGet.fin]
  conv_rhs => erw [GetMap.eq.MapGet.fin]
  conv_rhs => erw [GetTranspose.eq.Get.fin]
  rfl


-- created on 2026-08-07
