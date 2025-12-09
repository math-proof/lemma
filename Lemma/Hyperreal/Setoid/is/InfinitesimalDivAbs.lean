import Lemma.Hyperreal.Setoid.is.OrAndS
import sympy.core.power
import sympy.sets.fancyset
open Hyperreal


@[main, comm, mp, mpr]
private lemma main
-- given
  (a b : ℝ*) :
-- imply
  a ≈ b ↔ Infinitesimal (|a - b| / (1 + |a| + |b|)) := by
-- proof
  rw [Setoid.is.OrAndS]
  sorry


-- created on 2025-12-09
