import Lemma.Hyperreal.Setoid.is.OrAndS
open Hyperreal


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  Infinitesimal x ↔ x ≈ 0 := by
-- proof
  rw [Setoid.is.OrAndS]
  simp [Infinitesimal0]



-- created on 2025-12-29
