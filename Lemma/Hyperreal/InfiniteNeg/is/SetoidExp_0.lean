import Lemma.Hyperreal.InfiniteNeg.is.InfinitesimalExp
import Lemma.Hyperreal.Infinitesimal.is.Setoid_0
open Hyperreal


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  InfiniteNeg x ↔ x.exp ≈ 0 := by
-- proof
  rw [InfiniteNeg.is.InfinitesimalExp]
  rw [Infinitesimal.is.Setoid_0]


-- created on 2025-12-29
