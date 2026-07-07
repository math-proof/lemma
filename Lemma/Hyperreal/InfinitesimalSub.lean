import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalNeg
open Hyperreal


@[main]
private lemma Comm
  {a b : ℝ*} :
-- imply
  (a - b) → 0 ↔ (b - a) → 0 := by
-- proof
  rw [Infinitesimal.is.InfinitesimalNeg]
  simp


-- created on 2025-12-10
