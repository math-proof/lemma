import Lemma.Bool.NotAny.is.All_Not
import Lemma.Hyperreal.Infinite.is.All_GtAbs
open Hyperreal Bool


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  ¬x.Infinite ↔ ∃ δ : ℝ⁺, |x| ≤ δ := by
-- proof
  simp [Infinite.is.All_GtAbs]


-- created on 2025-12-16
