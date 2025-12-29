import Lemma.Hyperreal.InfinitePos.is.Infinite.Gt_0
import Lemma.Real.GtExp_0
open Hyperreal Real


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x.exp.Infinite ↔ x.exp.InfinitePos := by
-- proof
  rw [InfinitePos.is.Infinite.Gt_0]
  have := GtExp_0 x
  simp at this
  simp [this]


-- created on 2025-12-28
