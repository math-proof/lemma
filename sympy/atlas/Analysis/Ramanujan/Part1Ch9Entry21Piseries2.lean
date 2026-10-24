/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry21Piseries2.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry8Arcsin
import Lemma.Real.Part1Ch9Entry8Arcsin
import Mathlib.Topology.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry21Piseries2

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Filter Finset MeasureTheory
open Entry8Arcsin (chapter9OddHarmonic)

noncomputable section

def chapter9Chi3Term (j : ℕ) : ℝ :=
  1 / (((2 * j + 1 : ℕ) : ℝ) ^ 3)

def chapter9Chi3AtOne : ℝ :=
  ∑' j : ℕ, chapter9Chi3Term j

def chapter9Entry21CosineTerm (x : ℝ) (j : ℕ) : ℝ :=
  Real.cos (((4 * j + 2 : ℕ) : ℝ) * x) /
    (((2 * j + 1 : ℕ) : ℝ) ^ 3)

def chapter9Entry21LeftTerm (x : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  (-1 : ℝ) ^ j * chapter9OddHarmonic k * Real.tan x ^ (2 * k) /
    (((2 * k : ℕ) : ℝ) ^ 2)

def chapter9Entry21SineTerm (x : ℝ) (j : ℕ) : ℝ :=
  Real.sin (((4 * j + 2 : ℕ) : ℝ) * x) /
    (((2 * j + 1 : ℕ) : ℝ) ^ 2)

def chapter9TanLogTerm (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ 2 / 2 * Real.log |Real.tan x|

private def arctanTerm (t : ℝ) (i : ℕ) : ℝ :=
  (-1) ^ i * t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)

private def chapF (u : ℝ) : ℝ := u ^ 2 / Real.sin (2 * u)

private def leftDerivTerm (x : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * Real.tan x ^ (2 * j + 1) /
    (((((2 * (j + 1) : ℕ))) : ℝ) * Real.cos x ^ 2)

private def SrTerm (r x : ℝ) (j : ℕ) : ℝ :=
  r ^ (2 * j + 1) * Real.sin (((4 * j + 2 : ℕ) : ℝ) * x) /
    (((2 * j + 1 : ℕ) : ℝ) ^ 2)

private def CrTerm (r x : ℝ) (j : ℕ) : ℝ :=
  r ^ (2 * j + 1) * Real.cos (((4 * j + 2 : ℕ) : ℝ) * x) /
    (((2 * j + 1 : ℕ) : ℝ) ^ 3)

private def ArTerm (r x : ℝ) (j : ℕ) : ℝ :=
  r ^ (2 * j + 1) * Real.cos (((4 * j + 2 : ℕ) : ℝ) * x) /
    ((2 * j + 1 : ℕ) : ℝ)

private def abelW (r x : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp ((2 * x : ℝ) * Complex.I)

private def abelP (r x : ℝ) : ℝ := 1 + 2 * r * Real.cos (2 * x) + r ^ 2

private def abelM (r x : ℝ) : ℝ := 1 - 2 * r * Real.cos (2 * x) + r ^ 2

private def abelA (r x : ℝ) : ℝ :=
  (1 / 4 : ℝ) * (Real.log (abelP r x) - Real.log (abelM r x))

private def abelQ (r x : ℝ) : ℝ :=
  2 * r * (1 + r ^ 2) * Real.sin (2 * x) /
    ((1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.sin (2 * x) ^ 2)

private def abelFr (r x : ℝ) : ℝ :=
  (-(x ^ 2)) * abelA r x + x * (∑' j, SrTerm r x j) +
    (1 / 2 : ℝ) * ((∑' j, CrTerm r x j) - (∑' j, CrTerm r 0 j))

private def abelGr (r t : ℝ) : ℝ := t ^ 2 * abelQ r t
end
end Entry21Piseries2
end MathlibExt.Analysis.Ramanujan.Part1Ch9
