/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry16Corollary1JensenSeries.lean -/

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
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.SummableUniformlyOn
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Topology.Connected.Basic

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry16Corollary1JensenSeries

/-- Normalized finite Jensen summand (left side). -/
noncomputable def jensenF (x : ℂ) (n : ℝ) (N k : ℕ) : ℂ :=
  if k ≤ N then ((N.choose k : ℕ) : ℂ) * (x + (k : ℂ) * (n : ℂ)) ^ k *
    ((N : ℂ) - x - (k : ℂ) * (n : ℂ)) ^ (N - k) / (N : ℂ) ^ N
  else 0

/-- Normalized finite Jensen summand (right side). -/
noncomputable def jensenG (n : ℝ) (N j : ℕ) : ℂ :=
  if j ≤ N then ((Nat.descFactorial N j : ℕ) : ℂ) * (n : ℂ) ^ j *
    ((N : ℂ) ^ (N - j)) / (N : ℂ) ^ N
  else 0

/-- Pointwise limit of `jensenF`. -/
noncomputable def jensenL (x : ℂ) (n : ℝ) (k : ℕ) : ℂ :=
  (x + (k : ℂ) * (n : ℂ)) ^ k / ((Nat.factorial k : ℕ) : ℂ) *
    Complex.exp (-(x + (k : ℂ) * (n : ℂ)))

end Entry16Corollary1JensenSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
