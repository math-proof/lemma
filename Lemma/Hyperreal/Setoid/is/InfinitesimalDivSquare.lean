import Lemma.Hyperreal.Setoid.is.OrAndS
import sympy.core.power
import sympy.sets.fancyset
open Hyperreal


@[main, comm, mp, mpr]
private lemma main
-- given
  (a b : ℝ*) :
-- imply
  a ≈ b ↔ Infinitesimal ((a - b)² / (1 + a² + b²)) := by
-- proof
  rw [Setoid.is.OrAndS]
  constructor
  ·
    sorry
  ·
    sorry


-- created on 2025-12-09
-- updated on 2025-12-11
