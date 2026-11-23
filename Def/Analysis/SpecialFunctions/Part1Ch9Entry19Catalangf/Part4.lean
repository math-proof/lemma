/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.Basic
public import Theorem.Analysis.SpecialFunctions.Part1Ch9Entry19Catalangf.Part3

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry19Catalangf

open scoped Topology

open Filter

noncomputable section

/-- Difference `D(x) = S(cos x)+S(sin x) - ((π/2)log(2cos x)+T(tan x))`. -/
def chap9D (x : ℝ) : ℝ :=
  ((∑' k : ℕ, chap9S (Real.cos x) k) + (∑' k : ℕ, chap9S (Real.sin x) k))
    - (Real.pi / 2 * Real.log (2 * Real.cos x) + (∑' k : ℕ, chap9T (Real.tan x) k))

end
end Entry19Catalangf
end Ramanujan.Part1Ch9
end
