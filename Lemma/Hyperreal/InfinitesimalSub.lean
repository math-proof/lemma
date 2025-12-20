import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalNeg
open Hyperreal


@[main]
private lemma Comm
  {a b : ℝ*} :
-- imply
  Infinitesimal (a - b) ↔ Infinitesimal (b - a) := by
-- proof
  rw [Infinitesimal.is.InfinitesimalNeg]
  simp


-- created on 2025-12-10
