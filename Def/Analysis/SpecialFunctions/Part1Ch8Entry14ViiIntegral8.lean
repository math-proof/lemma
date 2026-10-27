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
# Ramanujan's Notebooks, Part I, Chapter 8, Entry 14(vii)

Closed form for ∫₀ˣ 1/(1+u⁸) du via arctan and log terms.
-/


namespace Ramanujan.Part1Ch8

namespace Entry14ViiIntegral8

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Entry14A (n : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, 1 / (1 + u ^ n)

end
end Entry14ViiIntegral8
end Ramanujan.Part1Ch8
