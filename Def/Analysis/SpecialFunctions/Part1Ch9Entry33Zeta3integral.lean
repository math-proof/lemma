/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.NumberTheory.Harmonic.Bounds

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9, Entry 33

∫ x cosⁿx sin(nx) over [0,π/2] evaluates via harmonic numbers.
-/


namespace Ramanujan.Part1Ch9

namespace Entry33Zeta3integral

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9Entry33Integrand (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos x ^ n * Real.sin ((n : ℝ) * x)

def chapter9Entry33WeightedIntegrand (n : ℕ) (x : ℝ) : ℝ :=
  x * Real.cos x ^ n * Real.sin ((n : ℝ) * x)

end
end Entry33Zeta3integral
end Ramanujan.Part1Ch9
