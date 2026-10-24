/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry14LambertSeries.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import sympy.atlas.Analysis.Calculus.EulerMaclaurinFormula
import Lemma.Real.Calculus.EulerMaclaurinFormula
import Lemma.Real.ExpSubOneMittagLeffler
import sympy.atlas.Analysis.SpecialFunctions.ExpSubOneMittagLeffler

/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 14

This file proves explicit finite asymptotic expansions, with error bounds, for the
Lambert series with summands `1 / (exp (j * x) - 1)` and `1 / (exp (j * x) + 1)`.

The namespaces `Entry10Centralbinomialexpansion` / `Entry10Centralbinomialfull` and the
two theorem names `ramanujan_part1_ch6_entry10_centralbinomialexpansion` /
`ramanujan_part1_ch6_entry10_centralbinomialfull` are frozen Wanted identifiers and are
kept unchanged.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch6

namespace Entry10Centralbinomialexpansion

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter6Entry14PlusCorrection (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range n,
    let k := j + 1
    (((2 : ℝ) ^ (2 * k) - 1) * (bernoulli (2 * k) : ℝ) ^ 2 *
      x ^ (2 * k - 1)) /
      (((2 * k : ℕ) : ℝ) * ((2 * k).factorial : ℝ))

def chapter6Entry14PlusTerm (x : ℝ) (j : ℕ) : ℝ :=
  1 / (Real.exp ((j + 1 : ℕ) * x) + 1)

def chapter6Entry14PlusSum (x : ℝ) : ℝ :=
  ∑' j : ℕ, chapter6Entry14PlusTerm x j

end

end Entry10Centralbinomialexpansion

namespace Entry10Centralbinomialfull

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter6Entry14MinusCorrection (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range n,
    let k := j + 1
    ((bernoulli (2 * k) : ℝ) ^ 2 * x ^ (2 * k - 1)) /
      (((2 * k : ℕ) : ℝ) * ((2 * k).factorial : ℝ))

def chapter6Entry14MinusTerm (x : ℝ) (j : ℕ) : ℝ :=
  1 / (Real.exp ((j + 1 : ℕ) * x) - 1)

def chapter6Entry14MinusSum (x : ℝ) : ℝ :=
  ∑' j : ℕ, chapter6Entry14MinusTerm x j

private def ch6Entry14_aterm (m : ℕ) : ℝ := 2 * Real.pi * (m + 1)

private def ch6Entry14_rterm (m : ℕ) (u : ℝ) : ℝ :=
  2 * u / (u ^ 2 + ch6Entry14_aterm m ^ 2)

private def ch6Entry14_cterm (m : ℕ) (z : ℂ) : ℂ :=
  1 / (z - Complex.I * ch6Entry14_aterm m) + 1 / (z + Complex.I * ch6Entry14_aterm m)

private def ch6Entry14_ctermDeriv (m k : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ k * k ! *
    ((z - Complex.I * ch6Entry14_aterm m) ^ (-1 - k : ℤ) +
      (z + Complex.I * ch6Entry14_aterm m) ^ (-1 - k : ℤ))

private def ch6Entry14_dterm (q : ℕ) (u : ℝ) (m : ℕ) : ℝ :=
  (ch6Entry14_ctermDeriv m q (u : ℂ)).re

private def ch6Entry14_derivBound (q m : ℕ) : ℝ :=
  2 * q.factorial / ch6Entry14_aterm m ^ (q + 1)

private def ch6Entry14_kernelCore (u : ℝ) : ℝ :=
  ∑' m : ℕ, ch6Entry14_rterm m u

private def ch6Entry14_kernel (u : ℝ) : ℝ :=
  -1 / 2 + ch6Entry14_kernelCore u

private noncomputable def ch6Entry14_periodicKernel (p : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun p (Int.fract x)

private noncomputable def ch6Entry14_endpointCorrection (n : ℕ) (x : ℝ) (J : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n,
    (bernoulli (2 * k) : ℝ) / ((2 * k).factorial : ℝ) *
      (x ^ (2 * k - 1) * iteratedDeriv (2 * k - 1) ch6Entry14_kernel (x * J))

private noncomputable def ch6Entry14_emRemainder (n : ℕ) (x : ℝ) (J : ℕ) : ℝ :=
  1 / ((2 * n + 1).factorial : ℝ) *
    ∫ t in (0 : ℝ)..J, ch6Entry14_periodicKernel (2 * n + 1) t *
      (x ^ (2 * n + 1) * iteratedDeriv (2 * n + 1) ch6Entry14_kernel (x * t))

private noncomputable def ch6Entry14_periodicOddBound (n : ℕ) : ℝ :=
  (2 * ((2 * n + 1).factorial : ℝ) / (2 * Real.pi) ^ (2 * n + 1)) *
    (Real.pi ^ 2 / 6)

private noncomputable def ch6Entry14_integralOddBound (n : ℕ) : ℝ :=
  (Real.pi * ((2 * n + 1).factorial : ℝ) /
    (2 * Real.pi) ^ (2 * n + 1)) * (Real.pi ^ 2 / 6)

private noncomputable def ch6Entry14_coarseRemainderBound (n : ℕ) (x : ℝ) : ℝ :=
  (1 / ((2 * n + 1).factorial : ℝ)) * ch6Entry14_periodicOddBound n *
    x ^ (2 * n) * ch6Entry14_integralOddBound n

private noncomputable def ch6Entry14_kernelAntiderivative (u : ℝ) : ℝ :=
  Real.log (1 - Real.exp (-u)) - Real.log u

private noncomputable def ch6Entry14_minusMain (n : ℕ) (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant / x - Real.log x / x + 1 / 4 -
    chapter6Entry14MinusCorrection n x

end
namespace Entry10Centralbinomialexpansion
noncomputable section
private noncomputable def ch6Entry14_minusMain (n : ℕ) (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant / x - Real.log x / x + 1 / 4 -
    chapter6Entry14MinusCorrection n x
end
end Entry10Centralbinomialexpansion
end MathlibExt.Analysis.Ramanujan.Part1Ch6
