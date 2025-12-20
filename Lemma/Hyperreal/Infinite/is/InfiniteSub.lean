import Lemma.Hyperreal.Infinite.is.InfiniteAdd
import Lemma.Hyperreal.InfiniteSub
import Lemma.Int.Sub.eq.Add_Neg
open Hyperreal Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinite.is.InfiniteSub |
| comm | Hyperreal.InfiniteSub.is.Infinite |
| mp   | Hyperreal.InfiniteSub.of.Infinite |
| mpr  | Hyperreal.Infinite.of.InfiniteSub |
| mp.mt | Hyperreal.NotInfinite.of.NotInfiniteSub |
| mpr.mt | Hyperreal.NotInfiniteSub.of.NotInfinite |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
-- given
  (x : ℝ*)
  (r : ℝ) :
-- imply
  Infinite x ↔ Infinite (x - r) := by
-- proof
  simp [Infinite.is.InfiniteAdd x (-r)]
  rfl


@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma left
-- given
  (r : ℝ)
  (x : ℝ*) :
-- imply
  Infinite x ↔ Infinite (r - x) := by
-- proof
  simp [Infinite.is.InfiniteAdd x (-r)]
  rw [Add_Neg.eq.Sub]
  simp [InfiniteSub.comm]


-- created on 2025-12-11
-- updated on 2025-12-20
