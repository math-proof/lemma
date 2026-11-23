/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Theorem.Analysis.SpecialFunctions.Part1Ch9Entry2.Part2

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry2

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Filter Finset Complex Topology MeasureTheory

noncomputable section

def entry2E (a : ℝ) : ℂ :=
  Complex.exp (↑(Real.pi * a) * Complex.I)

def entry2A (a : ℝ) : ℂ :=
  ((↑Real.pi) ^ 2 * entry2E a) / ((1 + entry2E a) ^ 2)

def entry2B (a : ℝ) : ℂ :=
  (-(↑Real.pi)) / (1 + entry2E a)

def entry2h (a : ℝ) (x : ℝ) : ℂ :=
  (entry2A a + entry2B a * ↑x) * Complex.exp (↑((a - 1) * x) * Complex.I)

end
end Entry2
end Ramanujan.Part1Ch9
end
