import sympy.series.limits
import sympy.core.singleton
import Lemma.Bool.Iff.is.IffNotS
open Bool


@[main, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  stdPart x = 0 ↔ x → ∞ ∨ x → 0 := by
-- proof
  rw [Iff.is.IffNotS]
  simp


-- created on 2025-12-18
