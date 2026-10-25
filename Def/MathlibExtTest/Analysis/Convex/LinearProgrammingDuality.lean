/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Convex/LinearProgrammingDuality.lean -/


import Theorem.Analysis.Convex.LinearProgrammingDuality.Part3
/-!
# Tests for strong linear programming duality

Focused checks for `LPDuality.strong_linear_programming_duality`: an ordinary
one-dimensional program whose optimum value is pinned down, plus the two
empty-index boundary cases (no primal variables, no constraints).
-/


namespace LinearProgrammingDualityTest

/-- Constraint matrix `(1)` of the one-dimensional test program, given an
explicit matrix type so that dot notation resolves to `Matrix.mulVec`. -/
def oneDimA : Matrix (Fin 1) (Fin 1) ℝ := ![![1]]

end LinearProgrammingDualityTest
