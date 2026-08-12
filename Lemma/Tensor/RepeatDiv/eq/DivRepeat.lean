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
  [Semifield α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : Fin s.length)
  (n : ℕ) :
-- imply
  (X / B).repeat dim n = X.repeat dim n / B := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.repeat
  dsimp only [HDiv.hDiv]
  let b := B.data[0]
  have h_flat :
      (((X.data.map (fun x => x / b)).splitAt ↑dim).map (List.Vector.repeat · n)).flatten =
        ((((X.data.splitAt ↑dim).map (List.Vector.repeat · n)).flatten).map (fun y => y / b)) := by
    rw [SplitAtMap.eq.MapSplitAt]
    rw [MapMap.eq.Map_Comp]
    have h_inner :
        ((X.data.splitAt ↑dim).map fun v =>
            List.Vector.repeat (v.map fun x => x / b) n) =
          ((X.data.splitAt ↑dim).map fun v =>
            (List.Vector.repeat v n).map fun x => x / b) := by
      congr 1
      funext v
      apply RepeatMap.eq.MapRepeat v (· / b)
    change ((X.data.splitAt ↑dim).map fun v =>
        List.Vector.repeat (v.map fun x => x / b) n).flatten =
      ((((X.data.splitAt ↑dim).map (List.Vector.repeat · n)).flatten).map fun y => y / b)
    rw [h_inner]
    conv_lhs =>
      arg 1
      rw [show (fun v => (v.repeat n).map fun x => x / b) =
              ((fun w => w.map fun x => x / b) ∘ (List.Vector.repeat · n)) from rfl]
      rw [Map_Comp.eq.MapMap]
    rw [FlattenMap.eq.MapFlatten]
  have h_prod := (ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength dim.isLt n).symm
  rw [MapCast.eq.Cast_Map.of.Eq h_prod]
  exact congrArg (cast (congrArg (List.Vector α) h_prod)) h_flat


-- created on 2026-08-12
