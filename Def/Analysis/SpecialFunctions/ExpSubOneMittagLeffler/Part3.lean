/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Theorem.Analysis.SpecialFunctions.ExpSubOneMittagLeffler.Part2
/-!
# Mittag-Leffler expansion of the Bose-Einstein kernel
-/


namespace MetaMathlibExt

open scoped BigOperators

open Complex

noncomputable section

/-- The analytic remainder after truncating the Laurent expansion of
`1 / (Real.exp v - 1)` after `N` odd-power terms. -/
def oneDivExpSubOneLaurentRemainder (N : ℕ) (v : ℝ) : ℝ :=
  if v = 0 then 0 else
    1 / (Real.exp v - 1) - 1 / v + 1 / 2 -
      ∑ n ∈ Finset.range N,
        (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          v ^ (2 * n + 1)

end
end MetaMathlibExt
