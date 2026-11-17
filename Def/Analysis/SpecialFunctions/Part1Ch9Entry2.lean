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
public import Instance.Analysis.SpecialFunctions.Part1Ch9Entry2

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

def chapter9Entry2ConstantTerm (r : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  1 / ((((2 * k + 1 : ℕ) : ℝ) - a) ^ r) +
    1 / ((((2 * k + 1 : ℕ) : ℝ) + a) ^ r)

def chapter9Entry2Constant (r : ℕ) (a : ℝ) : ℝ :=
  ∑' k : ℕ, chapter9Entry2ConstantTerm r a k

def chapter9Entry2CosineTerm (r : ℕ) (a x : ℝ) (k : ℕ) : ℝ :=
  Real.cos (((((2 * k + 1 : ℕ) : ℝ) - a) * x)) /
      ((((2 * k + 1 : ℕ) : ℝ) - a) ^ r) +
    Real.cos (((((2 * k + 1 : ℕ) : ℝ) + a) * x)) /
      ((((2 * k + 1 : ℕ) : ℝ) + a) ^ r)

def chapter9Entry2SineTerm (r : ℕ) (a x : ℝ) (k : ℕ) : ℝ :=
  Real.sin (((((2 * k + 1 : ℕ) : ℝ) - a) * x)) /
      ((((2 * k + 1 : ℕ) : ℝ) - a) ^ r) +
    Real.sin (((((2 * k + 1 : ℕ) : ℝ) + a) * x)) /
      ((((2 * k + 1 : ℕ) : ℝ) + a) ^ r)

end
end Entry2
end Ramanujan.Part1Ch9
end
