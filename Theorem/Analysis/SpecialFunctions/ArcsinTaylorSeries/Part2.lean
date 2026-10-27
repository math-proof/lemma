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
import Def.Analysis.SpecialFunctions.ArcsinTaylorSeries.Part2


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
