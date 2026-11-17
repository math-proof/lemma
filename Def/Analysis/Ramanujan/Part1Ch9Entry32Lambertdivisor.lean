/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry32Lambertdivisor.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
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
