/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# Ramanujan's Notebooks, Part I, Chapter 8, Entry 14(vi)

Closed form for ∫₀ˣ 1/(1+u⁶) du via arctan and log terms.
-/


namespace Ramanujan.Part1Ch8

namespace Entry14ViIntegral6

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Entry14A (n : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, 1 / (1 + u ^ n)

end
end Entry14ViIntegral6
end Ramanujan.Part1Ch8
