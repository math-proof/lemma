/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Data.Finset.Defs
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Basic

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch8

namespace Entry17Loggammaintegral

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Entry17Term (x : ℝ) (j : ℕ) : ℝ :=
  let k : ℝ := j + 1
  Real.log k / k - Real.log (k + x) / (k + x)

def chapter8Entry17Phi (x : ℝ) : ℝ :=
  ∑' j : ℕ, chapter8Entry17Term x j

def chapter8RealDigamma (x : ℝ) : ℝ :=
  deriv Real.Gamma x / Real.Gamma x

end
end Entry17Loggammaintegral
end Ramanujan.Part1Ch8
end
