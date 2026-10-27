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

def chapter9Entry1ConstantTerm (r : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  1 / ((((2 * k + 1 : ℕ) : ℝ) - a) ^ r) -
    1 / ((((2 * k + 1 : ℕ) : ℝ) + a) ^ r)

def chapter9Entry1Constant (r : ℕ) (a : ℝ) : ℝ :=
  ∑' k : ℕ, chapter9Entry1ConstantTerm r a k

def chapter9Entry1CosineTerm (r : ℕ) (a x : ℝ) (k : ℕ) : ℝ :=
  Real.cos (((((2 * k + 1 : ℕ) : ℝ) - a) * x)) /
      ((((2 * k + 1 : ℕ) : ℝ) - a) ^ r) -
    Real.cos (((((2 * k + 1 : ℕ) : ℝ) + a) * x)) /
      ((((2 * k + 1 : ℕ) : ℝ) + a) ^ r)

def chapter9Entry1SineTerm (r : ℕ) (a x : ℝ) (k : ℕ) : ℝ :=
  Real.sin (((((2 * k + 1 : ℕ) : ℝ) - a) * x)) /
      ((((2 * k + 1 : ℕ) : ℝ) - a) ^ r) -
    Real.sin (((((2 * k + 1 : ℕ) : ℝ) + a) * x)) /
      ((((2 * k + 1 : ℕ) : ℝ) + a) ^ r)

end
end Entry1Logratio
end Ramanujan.Part1Ch9
end
