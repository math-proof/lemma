import Lemma.Hyperreal.InfiniteNeg.is.Infinite.Lt_0
import Lemma.Hyperreal.InfinitePos.is.Infinite.Gt_0
open Hyperreal


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x.InfinitePos ↔ (-x).InfiniteNeg := by
-- proof
  simp [InfiniteNeg.is.Infinite.Lt_0, InfinitePos.is.Infinite.Gt_0]


-- created on 2025-12-29
