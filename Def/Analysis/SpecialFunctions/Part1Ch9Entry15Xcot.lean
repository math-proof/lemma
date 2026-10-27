/-
Author: @akiezun, Avocado
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-!
# Ramanujan's Notebooks, Part I, Chapter 9, Entry 15

X·cot x integral of order n reduces via a binomial recurrence.
-/


namespace Ramanujan.Part1Ch9

namespace Entry15Xcot

open scoped Nat Real BigOperators Interval Polynomial

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9CotPrimitive (n : ℕ) (x : ℝ) : ℝ :=
  ∫ u in Real.pi / 4..x, u ^ n * (Real.cos u / Real.sin u)

end
end Entry15Xcot
end Ramanujan.Part1Ch9
