import Lemma.Bool.And_Or.is.OrAndS
import Lemma.Hyperreal.InfiniteNeg.is.Infinite.Lt_0
import Lemma.Hyperreal.InfinitePos.is.Infinite.Gt_0
import Lemma.Hyperreal.Ne_0.of.Infinite
open Bool Hyperreal


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinite.is.InfinitePos.ou.InfiniteNeg |
| comm | Hyperreal.InfinitePos.ou.InfiniteNeg.is.Infinite |
| mp   | Hyperreal.InfinitePos.ou.InfiniteNeg.of.Infinite |
| mpr  | Hyperreal.Infinite.of.InfinitePos.ou.InfiniteNeg |
| mp.mt | Hyperreal.NotInfinite.of.NotInfinitePos.NotInfiniteNeg |
| mpr.mt| Hyperreal.NotInfinitePos.NotInfiniteNeg.of.NotInfinite |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x.Infinite ↔ x.InfinitePos ∨ x.InfiniteNeg := by
-- proof
  simp [InfinitePos.is.Infinite.Gt_0]
  simp [InfiniteNeg.is.Infinite.Lt_0]
  rw [OrAndS.is.And_Or]
  simp
  intro h
  have h := Ne_0.of.Infinite h
  aesop


-- created on 2025-12-26
