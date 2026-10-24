/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry26Ramanujanpi.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry24Dougall
import Lemma.Real.Part1Ch9Entry24Dougall
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Linarith

section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.

This module proves Entry 26, Ramanujan's Landen-type dilogarithm identity.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry26Ramanujanpi

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9BoundaryLog (x : ℝ) : ℝ :=
  if x = 0 then 0 else Real.log x

def chapter9DilogCosTerm (rho angle : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  rho ^ k * Real.cos ((k : ℝ) * angle) / ((k : ℝ) ^ 2)

def chapter9DilogSinTerm (rho angle : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  rho ^ k * Real.sin ((k : ℝ) * angle) / ((k : ℝ) ^ 2)

private def chapter9ComplexOddDilogTerm (z : ℂ) (j : ℕ) : ℂ :=
  z ^ (2 * j + 1) / ((((2 * j + 1 : ℕ)) : ℂ) ^ 2)

private def chapter9ComplexOddDilog (z : ℂ) : ℂ :=
  ∑' j : ℕ, chapter9ComplexOddDilogTerm z j

private def chapter9ComplexLogTerm (z : ℂ) (n : ℕ) : ℂ :=
  z ^ (n + 1) / (((n + 1 : ℕ)) : ℂ)

private def chapter9ComplexLogSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, chapter9ComplexLogTerm z n

private def chapter9ComplexOddLogTerm (z : ℂ) (j : ℕ) : ℂ :=
  z ^ (2 * j + 1) / ((((2 * j + 1 : ℕ)) : ℂ))

private def chapter9ComplexOddLogSeries (z : ℂ) : ℂ :=
  ∑' j : ℕ, chapter9ComplexOddLogTerm z j

private def chapter9MobiusW (z : ℂ) : ℂ := (1 - z) / (1 + z)

private def chapter9F (z : ℂ) : ℂ :=
  chapter9ComplexOddDilog z + chapter9ComplexOddDilog (chapter9MobiusW z) +
    (1 / 2 : ℂ) * Complex.log z * Complex.log (chapter9MobiusW z)

private def chapter9Domain : Set ℂ := {z | 0 < z.re ∧ ‖z‖ < 1}

private def e26_endpointParam (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private def e26_endpointPoint (n : ℕ) : ℂ :=
  chapter9MobiusW (e26_endpointParam n)

private def e26_approxPoint (z : ℂ) (n : ℕ) : ℂ :=
  ((1 - e26_endpointParam n : ℝ) : ℂ) * z + (e26_endpointParam n / 2 : ℝ)

private def e26_polar (r angle : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp (Complex.I * (angle : ℂ))
end
end Entry26Ramanujanpi
end MathlibExt.Analysis.Ramanujan.Part1Ch9
