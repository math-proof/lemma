/-
Author: @akiezun, Avocado
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 13

Generalized Stieltjes constants exist uniquely; γ₀ is Euler-Mascheroni.
-/


namespace Ramanujan.Part1Ch7

namespace Entry13Bernoullipolyadd

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7StieltjesApprox (k m : ℕ) : ℝ :=
  (∑ j ∈ Icc 1 m, Real.log (j : ℝ) ^ k / j) -
    Real.log (m : ℝ) ^ (k + 1) / (k + 1)

noncomputable def chapter7StieltjesFun (k : ℕ) (x : ℝ) : ℝ :=
  Real.log x ^ k / x

noncomputable def chapter7StieltjesInt (k : ℕ) (x : ℝ) : ℝ :=
  Real.log x ^ (k + 1) / ((k : ℝ) + 1)

end
end Entry13Bernoullipolyadd
end Ramanujan.Part1Ch7
