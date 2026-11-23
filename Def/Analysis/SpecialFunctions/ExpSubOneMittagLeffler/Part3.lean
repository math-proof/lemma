/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Tactic
public import Theorem.Analysis.SpecialFunctions.ExpSubOneMittagLeffler.Part2

@[expose] public section

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
