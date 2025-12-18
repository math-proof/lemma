import Lemma.Bool.NotAll.is.Any_Not
import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
open Hyperreal Bool


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  ¬Infinitesimal x ↔ ∃ δ : ℝ⁺, |x| ≥ δ := by
-- proof
  rw [Infinitesimal.is.All_LtAbs]
  simp [NotAll.is.Any_Not]


-- created on 2025-12-09
-- updated on 2025-12-16
