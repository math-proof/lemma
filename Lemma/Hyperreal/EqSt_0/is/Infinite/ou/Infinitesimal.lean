import Lemma.Bool.Iff.is.IffNotS
import Lemma.Hyperreal.NeSt_0.is.NotInfinite.NotInfinitesimal
open Hyperreal Bool


@[main, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x.st = 0 ↔ x.Infinite ∨ x.Infinitesimal := by
-- proof
  rw [Iff.is.IffNotS]
  simp [NeSt_0.is.NotInfinite.NotInfinitesimal]


-- created on 2025-12-18
