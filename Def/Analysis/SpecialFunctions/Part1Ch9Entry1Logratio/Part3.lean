/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Theorem.Analysis.SpecialFunctions.Part1Ch9Entry1Logratio.Part2
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry1Logratio

open scoped Nat Real BigOperators Interval Polynomial

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def entry1_oddLimit (r : ℕ) (a x : ℝ) : ℝ :=
  ∑ k ∈ range ((r - 1) / 2 + 1),
    (-1 : ℝ) ^ k * chapter9Entry1Constant (r - 2 * k) a *
      x ^ (2 * k) / ((2 * k).factorial : ℝ)

def entry1_evenLimit (r : ℕ) (a x : ℝ) : ℝ :=
  ∑ k ∈ range (r / 2),
    (-1 : ℝ) ^ k * chapter9Entry1Constant (r - 2 * k - 1) a *
      x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)

end
end Entry1Logratio
end Ramanujan.Part1Ch9
end
