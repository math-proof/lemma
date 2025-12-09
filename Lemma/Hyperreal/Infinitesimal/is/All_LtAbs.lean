import Lemma.Hyperreal.IsSt.is.All_LtAbs
open Hyperreal


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  Infinitesimal x ↔ ∀ δ : ℝ⁺, |x| < δ := by
-- proof
  unfold Infinitesimal
  simp [IsSt.is.All_LtAbs]


-- created on 2025-12-08
