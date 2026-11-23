/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Algebra.Polynomial.Smeval
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.RingTheory.Binomial
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.SpecialFunctions.ArcsinTaylorSeries.Part2

@[expose] public section

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
