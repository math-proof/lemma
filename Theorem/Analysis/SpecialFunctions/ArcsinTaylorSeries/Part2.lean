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
public import Def.Analysis.SpecialFunctions.ArcsinTaylorSeries.Part2

public section

namespace SpecialFunctions.ArcsinTaylorSeries

noncomputable section

/-- The normalized central-binomial coefficients are nonnegative. -/
theorem centralBinomialCoeff_nonneg (n : ℕ) : 0 ≤ centralBinomialCoeff n := by
  unfold centralBinomialCoeff
  positivity

/-- The normalized central-binomial coefficients are at most one. -/
theorem centralBinomialCoeff_le_one (n : ℕ) : centralBinomialCoeff n ≤ 1 :=
  centralBinomial_div_pow_le_one n

end
end SpecialFunctions.ArcsinTaylorSeries
