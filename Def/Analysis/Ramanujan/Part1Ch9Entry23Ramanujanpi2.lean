/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry23Ramanujanpi2.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Def.Analysis.Ramanujan.Part1Ch9Entry8Arcsin
import Lemma.Real.Part1Ch9Entry8Arcsin
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry23Ramanujanpi2

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Filter Finset Topology MeasureTheory

open Entry8Arcsin (chapter9OddHarmonic)

noncomputable section

def chapter9Entry23LeftTerm (x : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  (-1 : ℝ) ^ j * chapter9OddHarmonic k * Real.tan x ^ (2 * k) /
    (((2 * k : ℕ) : ℝ) ^ 2)

def chapter9Entry23FactorialTerm (u : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) *
      Real.sin u ^ (2 * k + 2) /
    (((2 * k + 1).factorial : ℝ) * (((2 * k + 2 : ℕ) : ℝ) ^ 2))

def chapter9Entry23Coeff (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / ((2 * k + 1).factorial : ℝ)

def chapter9Entry23ATerm (x : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * Real.tan x ^ (2 * (j + 1))
    / (((2 * (j + 1) : ℕ)) : ℝ)

def chapter9Entry23PTerm (t : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * t ^ (2 * j + 1)

def chapter9Entry23ArctanTerm (t : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * t ^ (2 * n + 1) / (((2 * n + 1 : ℕ)) : ℝ)

def chapter9Entry23KTerm (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * Real.sin u ^ (2 * k + 1)

def chapter9Entry23NTerm (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * Real.sin u ^ (2 * k + 2) / (((2 * k + 2 : ℕ)) : ℝ)

def chapter9Entry23ATerm' (x : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * Real.tan x ^ (2 * j + 1)
    / Real.cos x ^ 2

def chapter9Entry23LTerm' (x : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * Real.tan x ^ (2 * j + 1)
    / ((((2 * (j + 1) : ℕ)) : ℝ) * Real.cos x ^ 2)

def chapter9Entry23KTerm' (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * (((2 * k + 1 : ℕ)) : ℝ) * Real.sin u ^ (2 * k)
    * Real.cos u

def chapter9Entry23NTerm' (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * Real.sin u ^ (2 * k + 1) * Real.cos u

def chapter9Entry23STerm' (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * Real.sin u ^ (2 * k + 1) * Real.cos u
    / (((2 * k + 2 : ℕ)) : ℝ)

def chapter9Entry23CKTerm (u : ℝ) (k : ℕ) : ℝ :=
  Real.cos u * chapter9Entry23KTerm u k

def chapter9Entry23CKTerm' (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * (((2 * k + 1 : ℕ)) : ℝ) * Real.sin u ^ (2 * k)
    - chapter9Entry23Coeff k * (((2 * k + 2 : ℕ)) : ℝ)
      * Real.sin u ^ (2 * k + 2)

def chapter9Entry23ASeq (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * (((2 * k + 1 : ℕ)) : ℝ) * Real.sin u ^ (2 * k)

def chapter9Entry23BSeq (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * (((2 * k + 2 : ℕ)) : ℝ) * Real.sin u ^ (2 * k + 2)

end
end Entry23Ramanujanpi2
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
