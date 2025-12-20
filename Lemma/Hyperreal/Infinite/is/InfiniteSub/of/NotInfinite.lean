import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Int.Sub.eq.Add_Neg
open Hyperreal Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinite.is.InfiniteSub.of.NotInfinite |
| comm | Hyperreal.InfiniteSub.is.Infinite.of.NotInfinite |
| mp   | Hyperreal.InfiniteSub.of.Infinite.NotInfinite |
| mpr  | Hyperreal.Infinite.of.InfiniteSub.NotInfinite |
| mp.mt | Hyperreal.NotInfinite.of.NotInfiniteSub.NotInfinite |
| mpr.mt | Hyperreal.NotInfiniteSub.of.NotInfinite.NotInfinite |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬x.Infinite)
  (y : ℝ*) :
-- imply
  Infinite y ↔ Infinite (x - y) := by
-- proof
  have := Infinite.is.InfiniteAdd.of.NotInfinite h (-y)
  simp at this
  rw [Sub.eq.Add_Neg]
  rw [this]


-- created on 2025-12-20
