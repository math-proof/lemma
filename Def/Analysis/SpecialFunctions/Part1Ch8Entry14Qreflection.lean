/-
Author: @akiezun, Avocado
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# Ramanujan's Notebooks, Part I, Chapter 8, Entry 14

Closed form for ∫₀ˣ 1/(1+u¹⁰) du via arctan and log terms.
-/


namespace Ramanujan.Part1Ch8

namespace Entry14Qreflection

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Entry14A (n : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, 1 / (1 + u ^ n)

def chapter8Entry14A10Closed (x : ℝ) : ℝ :=
  Real.arctan x / 5 +
    Real.sqrt (6 + 2 * Real.sqrt 5) / 20 *
      Real.arctan (x * Real.sqrt (6 + 2 * Real.sqrt 5) /
        (2 * (1 - x ^ 2))) +
    Real.sqrt (6 - 2 * Real.sqrt 5) / 20 *
      Real.arctan (x * Real.sqrt (6 - 2 * Real.sqrt 5) /
        (2 * (1 - x ^ 2))) +
    Real.sqrt (10 + 2 * Real.sqrt 5) / 40 *
      Real.log ((1 + x * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + x ^ 2) /
        (1 - x * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + x ^ 2)) +
    Real.sqrt (10 - 2 * Real.sqrt 5) / 40 *
      Real.log ((1 + x * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + x ^ 2) /
        (1 - x * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + x ^ 2))

end
end Entry14Qreflection
end Ramanujan.Part1Ch8
