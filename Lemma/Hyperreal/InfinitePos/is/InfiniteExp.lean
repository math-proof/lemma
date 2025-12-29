import Lemma.Hyperreal.InfiniteExp.is.InfinitePosExp
import Lemma.Hyperreal.InfinitePos.is.InfinitePosExp
open Hyperreal


@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x.InfinitePos ↔ x.exp.Infinite := by
-- proof
  rw [InfiniteExp.is.InfinitePosExp]
  apply InfinitePos.is.InfinitePosExp


-- created on 2025-12-28
