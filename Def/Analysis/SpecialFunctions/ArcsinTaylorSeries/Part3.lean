/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Algebra.Polynomial.Smeval
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Data.Nat.Choose.Central
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Analysis.SpecialFunctions.ArcsinTaylorSeries.Part2


namespace SpecialFunctions.ArcsinTaylorSeries

noncomputable section

/-- The central-binomial Taylor series for `Real.arcsin`. -/
def arcsinSeries (t : ℝ) : ℝ :=
  ∑' n : ℕ, centralBinomialCoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

/-- The termwise integral of `arcsinSeries t / t`, normalized to vanish at zero. -/
def arcsinIntegralSeries (t : ℝ) : ℝ :=
  ∑' n : ℕ, centralBinomialCoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2

end
end SpecialFunctions.ArcsinTaylorSeries
