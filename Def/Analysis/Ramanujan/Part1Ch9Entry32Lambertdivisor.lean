/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry32Lambertdivisor.lean -/

/-
Author: @akiezun, Avocado
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
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry32Lambertdivisor

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9Entry19TanTerm (x : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * Real.tan x ^ (2 * k + 1) /
    (((2 * k + 1 : ℕ) : ℝ) ^ 2)

def chapter9Entry32LeftTerm (x : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * (k.factorial : ℝ) ^ 2 *
      Real.sin (2 * x) ^ (2 * k + 1) /
    (((2 * k).factorial : ℝ) * (((2 * k + 1 : ℕ) : ℝ) ^ 2))

-- Helper: central coefficient b k = 4^k (k!)^2 / (2k)!
noncomputable def bCoeff32 (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / (((2 * k).factorial : ℝ))

noncomputable def aCoeff32 (k : ℕ) : ℝ :=
  bCoeff32 k / (((2 * k + 1 : ℕ)) : ℝ)

noncomputable def S32 (z : ℝ) : ℝ :=
  ∑' k : ℕ, aCoeff32 k * z ^ k

noncomputable def F32 (s : ℝ) : ℝ :=
  ∑' k : ℕ, bCoeff32 k * s ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)

noncomputable def G32 (t : ℝ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)

noncomputable def S32partial (N : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, aCoeff32 k * z ^ k

noncomputable def S32partialDeriv (N : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, aCoeff32 k * (k : ℝ) * z ^ (k - 1)

noncomputable def mu32 (z : ℝ) : ℝ := √(z * (1 - z))

noncomputable def A32 (z : ℝ) : ℝ := Real.arcsin (√z)

noncomputable def H32 (z : ℝ) : ℝ := mu32 z * S32 z

noncomputable def D32 (z : ℝ) : ℝ := H32 z - A32 z

noncomputable def s32_of_t (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)

noncomputable def Phi32 (t : ℝ) : ℝ :=
  F32 (s32_of_t t) - 2 * G32 t

end
end Entry32Lambertdivisor
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
