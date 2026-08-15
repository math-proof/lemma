import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.MapData.eq.DataMap
import Lemma.Vector.FlattenMap.eq.MapFlatten
import Lemma.Vector.GetMap.eq.UFnGet
import sympy.tensor.tensor
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.MapGetSlice.eq.GetSliceMap |
| comm | Tensor.GetSliceMap.eq.MapGetSlice |
-/
@[main, comm]
private lemma main
  {β : Type*}
-- given
  (X : Tensor α (n :: s))
  (f : α → β)
  (slice : Slice) :
-- imply
  (X.getSlice slice).map f = (X.map f).getSlice slice := by
-- proof
  apply Eq.of.EqDataS
  rw [DataMap.eq.MapData]
  unfold Tensor.getSlice
  simp
  erw [MapFlatten.eq.FlattenMap]
  apply congrArg List.Vector.flatten
  apply List.Vector.ext
  intro t
  rw [GetMap.eq.UFnGet]
  erw [GetMap.eq.UFnGet]
  erw [GetMap.eq.UFnGet]
  simp [Tensor.length]
  rw [MapData.eq.DataMap]
  apply congrArg Tensor.data
  erw [MapGet.eq.GetMap]
  apply Eq.of.EqDataS
  rfl


-- created on 2026-08-15
