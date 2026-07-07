import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Hyperreal.Infinite.is.InfiniteNeg
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
  (h : ¬x → ∞)
  (y : ℝ*) :
-- imply
  y → ∞ ↔ (x - y) → ∞ := by
-- proof
  have := Infinite.is.InfiniteAdd.of.NotInfinite h (-y)
  rw [InfiniteNeg.is.Infinite] at this
  rwa [Sub.eq.Add_Neg]


-- created on 2025-12-20
