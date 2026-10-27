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
import Theorem.Analysis.SpecialFunctions.Part1Ch9Entry2.Part6
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

def entry2CosSummand (r : ℕ) (a : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 2 * k) a *
    y ^ (2 * k) / ((2 * k).factorial : ℝ)

def entry2CosPi (r : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (r / 2) * Real.pi * x ^ (r - 1) / (2 * ((r - 1).factorial : ℝ))

def entry2Pcos (r : ℕ) (a x : ℝ) : ℝ :=
  (∑ k ∈ range (r / 2), entry2CosSummand r a k x) + entry2CosPi r x

def entry2SinSummand (r : ℕ) (a : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 1 - 2 * k) a *
    y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)

def entry2SinPi (r : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ ((r - 1) / 2) * Real.pi * x ^ (r - 1) / (2 * ((r - 1).factorial : ℝ))

def entry2Psin (r : ℕ) (a x : ℝ) : ℝ :=
  (∑ k ∈ range ((r - 1) / 2), entry2SinSummand r a k x) + entry2SinPi r x

def entry2CosSummandDeriv (r : ℕ) (a x : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 2 * k) a *
    ((((2 * k : ℕ)) : ℝ) * x ^ (2 * k - 1)) / ((2 * k).factorial : ℝ)

def entry2CosPiDeriv (r : ℕ) (x : ℝ) : ℝ :=
  ((-1 : ℝ) ^ (r / 2) * Real.pi) * ((((r - 1 : ℕ)) : ℝ) * x ^ ((r - 1) - 1)) /
    (2 * ((r - 1).factorial : ℝ))

def entry2SinSummandDeriv (r : ℕ) (a x : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 1 - 2 * k) a *
    ((((2 * k + 1 : ℕ)) : ℝ) * x ^ (2 * k + 1 - 1)) / ((2 * k + 1).factorial : ℝ)

def entry2SinPiDeriv (r : ℕ) (x : ℝ) : ℝ :=
  ((-1 : ℝ) ^ ((r - 1) / 2) * Real.pi) * ((((r - 1 : ℕ)) : ℝ) * x ^ ((r - 1) - 1)) /
    (2 * ((r - 1).factorial : ℝ))

end
end Entry2
end Ramanujan.Part1Ch9
end
