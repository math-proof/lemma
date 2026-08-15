import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.FlattenMap.eq.MapFlatten
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.MapMap.eq.Map_Comp
import Lemma.Vector.ResizeMap.eq.MapResize
import Lemma.Vector.SplitAtMap.eq.MapSplitAt
import sympy.tensor.tensor
open List Tensor Vector


@[main]
private lemma main
  [Zero α]
  {f : α → α → α}
-- given
  (h0 : ∀ b : α, f 0 b = 0)
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : Fin s.length)
  (n : ℕ) :
-- imply
  (X.map (f · B.data[0])).resize dim n = (X.resize dim n).map (f · B.data[0]) := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.resize Tensor.map
  let b := B.data[0]
  let r := n * (s.drop dim.succ).prod
  have h_prod := MulProd_Mul_Prod.eq.ProdSet.of.GtLength dim.isLt n
  rw [MapCast.eq.Cast_Map.of.Eq h_prod]
  apply congrArg (cast (congrArg (List.Vector α) h_prod))
  rw [SplitAtMap.eq.MapSplitAt]
  rw [MapMap.eq.Map_Comp]
  have h_inner : ((X.data.splitAt ↑dim).map fun v => List.Vector.resize (v.map fun x => f x b) r) = ((X.data.splitAt ↑dim).map fun v => (List.Vector.resize v r).map fun x => f x b) := by
    congr 1
    funext v
    apply ResizeMap.eq.MapResize (h0 b)
  change ((X.data.splitAt ↑dim).map fun v => List.Vector.resize (v.map fun x => f x b) r).flatten = ((((X.data.splitAt ↑dim).map (List.Vector.resize · r)).flatten).map fun y => f y b)
  rw [h_inner]
  conv_lhs =>
    arg 1
    rw [show (fun v => (v.resize r).map fun x => f x b) = ((fun w => w.map fun x => f x b) ∘ (List.Vector.resize · r)) from rfl]
    rw [Map_Comp.eq.MapMap]
  rw [FlattenMap.eq.MapFlatten]


-- created on 2026-08-15
