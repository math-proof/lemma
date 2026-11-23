/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry15Treeseries.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Def.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
public import Theorem.Nat.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
public import Theorem.Nat.Ramanujan.Part1Ch3Section8Example4Integrable
public import Def.NumberTheory.Ramanujan.Part1Ch3Section8Example4Integrable
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry15Treeseries

/-- Tree-function coefficient: `(n+1)^(n-1)/n!`, matching the wanted summand factor. -/
noncomputable def treeCoeff (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (n - 1) / (Nat.factorial n : ℝ)

/-- Tree series `S(w) = ∑ (n+1)^(n-1)/n! * w^n`. -/
noncomputable def treeSeries (w : ℝ) : ℝ :=
  ∑' n : ℕ, treeCoeff n * w ^ n

/-- Derivative series `D(w) = ∑ (n+1) * c(n+1) * w^n`. -/
noncomputable def treeSeriesD (w : ℝ) : ℝ :=
  ∑' n : ℕ, (((n : ℝ) + 1) * treeCoeff (n + 1) * w ^ n)

/-- Auxiliary series `E(w) = ∑ (n+1) * c(n) * w^n`. -/
noncomputable def treeSeriesE (w : ℝ) : ℝ :=
  ∑' n : ℕ, (((n : ℝ) + 1) * treeCoeff n * w ^ n)

/-- Radius of convergence `ρ₀ = exp (-1)`. -/
noncomputable def rho0 : ℝ := Real.exp (-1)

end Entry15Treeseries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
