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
  [Semifield α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : Fin s.length)
  (n : ℕ) :
-- imply
  (X / B).resize dim n = X.resize dim n / B := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.resize
  dsimp only [HDiv.hDiv]
  let b := B.data[0]
  let r := n * (s.drop dim.succ).prod
  have h_flat :
      (((X.data.map (fun x => x / b)).splitAt ↑dim).map (List.Vector.resize · r)).flatten =
        ((((X.data.splitAt ↑dim).map (List.Vector.resize · r)).flatten).map (fun y => y / b)) := by
    rw [SplitAtMap.eq.MapSplitAt]
    rw [MapMap.eq.Map_Comp]
    have h_inner :
        ((X.data.splitAt ↑dim).map fun v => List.Vector.resize (v.map fun x => x / b) r) =
          ((X.data.splitAt ↑dim).map fun v => (List.Vector.resize v r).map fun x => x / b) := by
      congr 1
      funext v
      apply ResizeMap.eq.MapResize (zero_div b)
    change ((X.data.splitAt ↑dim).map fun v => List.Vector.resize (v.map fun x => x / b) r).flatten =
      ((((X.data.splitAt ↑dim).map (List.Vector.resize · r)).flatten).map fun y => y / b)
    rw [h_inner]
    conv_lhs =>
      arg 1
      rw [show (fun v => (v.resize r).map fun x => x / b) =
              ((fun w => w.map fun x => x / b) ∘ (List.Vector.resize · r)) from rfl]
      rw [Map_Comp.eq.MapMap]
    rw [FlattenMap.eq.MapFlatten]
  have h_prod := MulProd_Mul_Prod.eq.ProdSet.of.GtLength dim.isLt n
  rw [show r = n * (s.drop dim.succ).prod from rfl] at h_flat
  rw [MapCast.eq.Cast_Map.of.Eq h_prod]
  exact congrArg (cast (congrArg (List.Vector α) h_prod)) h_flat


-- created on 2026-08-12
