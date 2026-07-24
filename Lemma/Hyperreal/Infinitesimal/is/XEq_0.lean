import Lemma.Hyperreal.XEq.is.OrAndS
open Hyperreal


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x → 0 ↔ x ≈ 0 := by
-- proof
  rw [XEq.is.OrAndS]
  simp



-- created on 2025-12-29
