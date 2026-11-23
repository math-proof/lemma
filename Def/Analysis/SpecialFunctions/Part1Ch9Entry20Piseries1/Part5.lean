/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.SpecialFunctions.Part1Ch9Entry20Piseries1.Part4

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry20Piseries1

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def auxH_term (x : ℝ) (k : ℕ) : ℝ :=
  auxA k * Real.sin x ^ (2 * k + 2) / ((((2 * k + 2 : ℕ)) : ℝ))

def auxH (x : ℝ) : ℝ := ∑' k : ℕ, auxH_term x k

end
end Entry20Piseries1
end Ramanujan.Part1Ch9
end
