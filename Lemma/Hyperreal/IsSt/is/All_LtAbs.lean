import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
open Hyperreal


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*)
  (r : ℝ) :
-- imply
  ((x - r) → 0) ↔ ∀ δ : ℝ⁺, |x - r| < δ := by
-- proof
  rw [Infinitesimal.is.All_LtAbs]


-- created on 2025-12-08
