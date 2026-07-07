import Lemma.Hyperreal.IsSt.is.Le0Mk.EqStdPart
open Hyperreal


@[main]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  (∃ r : ℝ, (x - r) → 0) ↔ ¬x → ∞ := by
-- proof
  simp [IsSt.is.Le0Mk.EqStdPart]


-- created on 2025-12-18
