/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9, Entry 8

Odd-harmonic power series at x/(2-x) equals (log(1-x))²/8 + Li₂(x)/2.
-/


namespace Ramanujan.Part1Ch9

namespace Entry8Arcsin

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9Entry8DilogTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)

def chapter9Entry8Dilog (x : ℝ) : ℝ :=
  ∑' n : ℕ, chapter9Entry8DilogTerm x n

def chapter9OddHarmonic (n : ℕ) : ℝ :=
  ∑ j ∈ range n, 1 / ((2 * j + 1 : ℕ) : ℝ)

def chapter9Entry8FTerm (x : ℝ) (n : ℕ) : ℝ :=
  chapter9OddHarmonic (n + 1) * x ^ (2 * n + 1) /
    ((2 * n + 1 : ℕ) : ℝ)

def chapter9Entry8F (x : ℝ) : ℝ :=
  ∑' n : ℕ, chapter9Entry8FTerm x n

end
end Entry8Arcsin
end Ramanujan.Part1Ch9
