import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.FlattenMap.eq.MapFlatten
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.MapMap.eq.Map_Comp
import Lemma.Vector.RepeatMap.eq.MapRepeat
import Lemma.Vector.SplitAtMap.eq.MapSplitAt
open List Tensor Vector


@[main]
private lemma main
-- given
  (f : α → α → α)
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : Fin s.length)
  (n : ℕ) :
-- imply
  (X.map (f · B.data[0])).repeat dim n = (X.repeat dim n).map (f · B.data[0]) := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.repeat Tensor.map
  let b := B.data[0]
  have h_prod := (ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength dim.isLt n).symm
  rw [MapCast.eq.Cast_Map.of.Eq h_prod]
  apply congrArg (cast (congrArg (List.Vector α) h_prod))
  rw [SplitAtMap.eq.MapSplitAt]
  rw [MapMap.eq.Map_Comp]
  have h_inner : ((X.data.splitAt ↑dim).map fun v => List.Vector.repeat (v.map fun x => f x b) n) = ((X.data.splitAt ↑dim).map fun v => (List.Vector.repeat v n).map fun x => f x b) := by
    congr 1
    funext v
    apply RepeatMap.eq.MapRepeat v (f · b)
  change ((X.data.splitAt ↑dim).map fun v =>
      List.Vector.repeat (v.map fun x => f x b) n).flatten = ((((X.data.splitAt ↑dim).map (List.Vector.repeat · n)).flatten).map fun y => f y b)
  rw [h_inner]
  conv_lhs =>
    arg 1
    rw [show (fun v => (v.repeat n).map fun x => f x b) = ((fun w => w.map fun x => f x b) ∘ (List.Vector.repeat · n)) from rfl]
    rw [Map_Comp.eq.MapMap]
  rw [FlattenMap.eq.MapFlatten]



-- created on 2026-08-15
