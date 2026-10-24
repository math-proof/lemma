/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry16Corollary1JensenSeries.lean -/

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
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Lemma.Nat.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Lemma.Nat.Ramanujan.Part1Ch3Section8Example4Integrable
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Section8Example4Integrable
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Connected.Basic

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry16Corollary1JensenSeries

/-- Normalized finite Jensen summand (left side). -/
private noncomputable def jensenF (x : ℂ) (n : ℝ) (N k : ℕ) : ℂ :=
  if k ≤ N then ((N.choose k : ℕ) : ℂ) * (x + (k : ℂ) * (n : ℂ)) ^ k *
    ((N : ℂ) - x - (k : ℂ) * (n : ℂ)) ^ (N - k) / (N : ℂ) ^ N
  else 0

/-- Normalized finite Jensen summand (right side). -/
private noncomputable def jensenG (n : ℝ) (N j : ℕ) : ℂ :=
  if j ≤ N then ((Nat.descFactorial N j : ℕ) : ℂ) * (n : ℂ) ^ j *
    ((N : ℂ) ^ (N - j)) / (N : ℂ) ^ N
  else 0

/-- Pointwise limit of `jensenF`. -/
private noncomputable def jensenL (x : ℂ) (n : ℝ) (k : ℕ) : ℂ :=
  (x + (k : ℂ) * (n : ℂ)) ^ k / ((Nat.factorial k : ℕ) : ℂ) *
    Complex.exp (-(x + (k : ℂ) * (n : ℂ)))
end Entry16Corollary1JensenSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
