/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry21Piseries2.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Def.Analysis.Ramanujan.Part1Ch9Entry8Arcsin
public import Theorem.Real.Part1Ch9Entry8Arcsin
public import Mathlib.Topology.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

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

def arctanTerm (t : ℝ) (i : ℕ) : ℝ :=
  (-1) ^ i * t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)

def chapF (u : ℝ) : ℝ := u ^ 2 / Real.sin (2 * u)

def leftDerivTerm (x : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * Real.tan x ^ (2 * j + 1) /
    (((((2 * (j + 1) : ℕ))) : ℝ) * Real.cos x ^ 2)

def SrTerm (r x : ℝ) (j : ℕ) : ℝ :=
  r ^ (2 * j + 1) * Real.sin (((4 * j + 2 : ℕ) : ℝ) * x) /
    (((2 * j + 1 : ℕ) : ℝ) ^ 2)

def CrTerm (r x : ℝ) (j : ℕ) : ℝ :=
  r ^ (2 * j + 1) * Real.cos (((4 * j + 2 : ℕ) : ℝ) * x) /
    (((2 * j + 1 : ℕ) : ℝ) ^ 3)

def ArTerm (r x : ℝ) (j : ℕ) : ℝ :=
  r ^ (2 * j + 1) * Real.cos (((4 * j + 2 : ℕ) : ℝ) * x) /
    ((2 * j + 1 : ℕ) : ℝ)

def abelW (r x : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp ((2 * x : ℝ) * Complex.I)

def abelP (r x : ℝ) : ℝ := 1 + 2 * r * Real.cos (2 * x) + r ^ 2

def abelM (r x : ℝ) : ℝ := 1 - 2 * r * Real.cos (2 * x) + r ^ 2

def abelA (r x : ℝ) : ℝ :=
  (1 / 4 : ℝ) * (Real.log (abelP r x) - Real.log (abelM r x))

def abelQ (r x : ℝ) : ℝ :=
  2 * r * (1 + r ^ 2) * Real.sin (2 * x) /
    ((1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.sin (2 * x) ^ 2)

def abelFr (r x : ℝ) : ℝ :=
  (-(x ^ 2)) * abelA r x + x * (∑' j, SrTerm r x j) +
    (1 / 2 : ℝ) * ((∑' j, CrTerm r x j) - (∑' j, CrTerm r 0 j))

def abelGr (r t : ℝ) : ℝ := t ^ 2 * abelQ r t

end
end Entry21Piseries2
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
