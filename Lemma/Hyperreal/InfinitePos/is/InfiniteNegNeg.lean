import Lemma.Hyperreal.InfinitePos.is.Infinite.Gt_0
open Hyperreal


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x → +∞ ↔ (-x) → -∞ := by
-- proof
  simp [InfinitePos.is.Infinite.Gt_0]


-- created on 2025-12-29
