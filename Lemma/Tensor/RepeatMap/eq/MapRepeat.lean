import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.FlattenMap.eq.MapFlatten
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.MapMap.eq.Map_Comp
import Lemma.Vector.RepeatMap.eq.MapRepeat
import Lemma.Vector.SplitAtMap.eq.MapSplitAt
open List Tensor Vector


@[main, comm]
private lemma main
  {f : α → β}
-- given
  (X : Tensor α s)
  (dim : Fin s.length)
  (n : ℕ) :
-- imply
  (X.map f).repeat dim n = (X.repeat dim n).map f := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.repeat Tensor.map
  have h_prod := (ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength dim.isLt n).symm
  rw [MapCast.eq.Cast_Map.of.Eq h_prod]
  apply congrArg (cast (congrArg (List.Vector β) h_prod))
  rw [SplitAtMap.eq.MapSplitAt]
  rw [MapMap.eq.Map_Comp]
  have h_inner : ((X.data.splitAt ↑dim).map fun v => List.Vector.repeat (v.map f) n) =
      ((X.data.splitAt ↑dim).map fun v => (List.Vector.repeat v n).map f) := by
    congr 1
    funext v
    apply RepeatMap.eq.MapRepeat v f
  change ((X.data.splitAt ↑dim).map fun v =>
      List.Vector.repeat (v.map f) n).flatten =
    ((((X.data.splitAt ↑dim).map (List.Vector.repeat · n)).flatten).map f)
  rw [h_inner]
  conv_lhs =>
    arg 1
    rw [show (fun v => (v.repeat n).map f) = ((fun w => w.map f) ∘ (List.Vector.repeat · n)) from rfl]
    rw [Map_Comp.eq.MapMap]
  rw [FlattenMap.eq.MapFlatten]


-- created on 2026-08-16
