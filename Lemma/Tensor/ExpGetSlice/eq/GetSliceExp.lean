import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.GetExp.eq.ExpGet
import Lemma.Vector.ExpFlatten.eq.FlattenExp
import Lemma.Vector.GetMap.eq.UFnGet
open Tensor Vector


@[main]
private lemma main
  [Exp α]
-- given
  (X : Tensor α (n :: s))
  (slice : Slice) :
-- imply
  exp (X.getSlice slice) = (exp X).getSlice slice := by
-- proof
  apply Eq.of.EqDataS
  rw [DataExp.eq.ExpData]
  unfold Tensor.getSlice
  simp
  erw [ExpFlatten.eq.FlattenExp]
  congr
  apply List.Vector.ext
  intro t
  rw [Vector.GetExp.eq.ExpGet.fin]
  erw [GetMap.eq.UFnGet]
  erw [GetMap.eq.UFnGet]
  rw [← DataExp.eq.ExpData]
  apply congrArg Tensor.data
  simp [Tensor.length]
  erw [ExpGet.eq.GetExp]
  apply Eq.of.EqDataS
  rfl


-- created on 2026-08-14
-- updated on 2026-08-15
