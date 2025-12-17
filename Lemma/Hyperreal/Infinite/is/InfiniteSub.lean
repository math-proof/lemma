import Lemma.Hyperreal.Infinite.is.InfiniteAdd
open Hyperreal


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


-- created on 2025-12-11
