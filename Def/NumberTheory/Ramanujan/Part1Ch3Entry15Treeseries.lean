/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry15Treeseries.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Def.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Lemma.Nat.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Lemma.Nat.Ramanujan.Part1Ch3Section8Example4Integrable
import Def.NumberTheory.Ramanujan.Part1Ch3Section8Example4Integrable
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Order.IntermediateValue
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
