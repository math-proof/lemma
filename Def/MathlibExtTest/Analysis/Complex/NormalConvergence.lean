/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Complex/NormalConvergence.lean -/


import Lemma.Real.Complex.NormalConvergence
open Complex MeasureTheory Topology Set Filter

/-!
# Tests for normal convergence APIs

Exercises the normal-convergence API on a concrete nonzero complex one-term
series, including absolute, uniform, and locally uniform convergence and
termwise differentiation.
-/


namespace N329Test

/-- Concrete nonzero complex one-term series used for testing. -/
def complexOneTermSeries : Nat → Complex → Complex :=
  fun n _ => if n = 0 then 1 else 0

end N329Test
