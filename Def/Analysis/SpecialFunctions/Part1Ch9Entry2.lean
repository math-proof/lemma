/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.AddCircle.Defs
import Instance.Analysis.SpecialFunctions.Part1Ch9Entry2
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
