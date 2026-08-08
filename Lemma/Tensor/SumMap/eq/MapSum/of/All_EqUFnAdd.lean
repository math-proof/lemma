import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Bool.EqCast.of.SEq
import Lemma.Vector.MapAdd.eq.AddMap.of.All_EqUFnAdd
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.MapData.eq.DataMap
import Lemma.Vector.FlattenMap.eq.MapFlatten
import Lemma.Vector.GetSum.eq.SumMapGet
import Lemma.Vector.MapMap.eq.Map_Comp
import Lemma.Vector.MapSum.eq.SumMap.of.All_EqUFnAdd
import Lemma.Vector.SplitAtMap.eq.MapSplitAt
open Tensor Vector Bool


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.SumMap.eq.MapSum.of.All_EqUFnAdd |
| comm | Tensor.MapSum.eq.SumMap.of.All_EqUFnAdd |
-/
@[main, comm]
private lemma main
  [AddCommMonoid α]
  [AddCancelCommMonoid β]
  {f : α → β}
  (hf : ∀ a b, f (a + b) = f a + f b)
  (X : Tensor α s)
  (i : ℕ) :
-- imply
  (X.map f).sum i = (X.sum i).map f := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.map Tensor.sum
  rw [SplitAtMap.eq.MapSplitAt X.data i f]
  rw [MapMap.eq.Map_Comp]
  conv_lhs =>
    pattern Function.comp _ _
    ext data
    simp only [Function.comp]
    rw [SplitAtMap.eq.MapSplitAt]
    rw [SumMap.eq.MapSum.of.All_EqUFnAdd (MapAdd.eq.AddMap.of.All_EqUFnAdd hf)]
  rw [MapCast.eq.Cast_Map.of.Eq (by simp [List.ProdEraseIdx.eq.MulProdS])]
  apply EqCastS.of.SEq.Eq (by simp; grind)
  simp [MapFlatten.eq.FlattenMap]
  rfl


-- created on 2026-08-08
