/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry22Chudnovsky.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry20Piseries1
import Lemma.Real.Part1Ch9Entry20Piseries1
import Lemma.Real.Ramanujan.Part1Ch9Entry21Piseries2
import Lemma.Real.ArcsinCentralBinomialReciprocal
import Lemma.Real.ArcsinTaylorSeries
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry21Piseries2
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import sympy.atlas.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal
import sympy.atlas.Analysis.SpecialFunctions.ArcsinTaylorSeries
section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.

This module proves `ramanujan_part1_ch9_entry22_chudnovsky`, Entry 22 on the
corrected range `0 ≤ x ≤ π / 4`.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry22Chudnovsky

open MathlibExt.Analysis.SpecialFunctions.ArcsinTaylorSeries

open scoped Nat Real BigOperators Interval
open Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9Chi3Term (j : ℕ) : ℝ :=
  1 / (((2 * j + 1 : ℕ) : ℝ) ^ 3)

def chapter9Chi3AtOne : ℝ :=
  ∑' j : ℕ, chapter9Chi3Term j

def chapter9Entry22CentralTerm (x : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose (2 * k) k : ℝ) * Real.cos x ^ (2 * k + 1) /
    ((2 : ℝ) ^ (2 * k) * (((2 * k + 1 : ℕ) : ℝ) ^ 2))

def chapter9Entry23FactorialTerm (u : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) *
      Real.sin u ^ (2 * k + 2) /
    (((2 * k + 1).factorial : ℝ) * (((2 * k + 2 : ℕ) : ℝ) ^ 2))

def chapter9Entry22LeftTerm (x : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23FactorialTerm x k +
    chapter9Entry23FactorialTerm (Real.pi / 2 - x) k

private def aCoeff (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) /
    (((2 * k + 1).factorial : ℝ))

private def e22A (t : ℝ) : ℝ :=
  ∑' m : ℕ, aCoeff m * t ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ)

private def e22S (t : ℝ) : ℝ :=
  ∑' m : ℕ, aCoeff m * t ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ) ^ 2

private def e22H (x : ℝ) : ℝ :=
  (e22S (Real.sin x) + e22S (Real.cos x))
    - (-(Real.pi ^ 2 / 8) * Real.log (2 * Real.cos x)
      + Real.pi / 2 * arcsinIntegralSeries (Real.cos x)
      + (1 / 4 : ℝ) * e22S (Real.sin (2 * x))
      - (1 / 2 : ℝ) * chapter9Chi3AtOne)

private def e22Q (u : ℝ) : ℝ := u * Real.cos u / (2 * Real.sinc u)

private def e22K (u : ℝ) : ℝ := u ^ 2 / 2 * Real.log (Real.sin u)

private def e22R (r : ℝ) (n : ℕ) : ℝ :=
  r ^ (n + 1) * (1 - (-1 : ℝ) ^ (n + 1)) / (4 * (((n : ℝ) + 1) ^ 3))

private def e22M (u : ℝ) : ℝ :=
  arcsinIntegralSeries (Real.sin u) - u * Real.log (Real.sin u)
end
end Entry22Chudnovsky
end MathlibExt.Analysis.Ramanujan.Part1Ch9
