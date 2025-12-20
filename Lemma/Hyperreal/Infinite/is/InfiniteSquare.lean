import Lemma.Hyperreal.Infinite.is.InfinitePow
open Hyperreal


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinite.is.InfiniteSquare |
| comm | Hyperreal.InfiniteSquare.is.Infinite |
| mp   | Hyperreal.InfiniteSquare.of.Infinite |
| mpr  | Hyperreal.Infinite.of.InfiniteSquare |
| mp.mt | Hyperreal.NotInfinite.of.NotInfiniteSquare |
| mpr.mt | Hyperreal.NotInfiniteSquare.of.NotInfinite |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x.Infinite ↔ x².Infinite :=
-- proof
  Infinite.is.InfinitePow (n := 2) x


-- created on 2025-12-20
