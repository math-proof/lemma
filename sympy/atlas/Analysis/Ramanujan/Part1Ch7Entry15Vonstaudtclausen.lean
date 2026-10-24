/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry15Vonstaudtclausen.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Phi
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Basic.Complex.BigOperators
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.Order.Compact

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry15Vonstaudtclausen

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7Entry15Left (r : ℂ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : ℂ :=
  (chapter7Phi r ⟨x - 1, by constructor <;> linarith⟩ -
      chapter7Phi r ⟨-x, by constructor <;> linarith⟩) /
    (4 * Complex.Gamma (r + 1))

def chapter7Entry15Term (r : ℂ) (x : ℝ) (k : ℕ) : ℂ :=
  (Real.sin (2 * Real.pi * k * x) : ℂ) /
    Complex.cpow (((2 * Real.pi * k : ℝ) : ℂ)) (r + 1)

def chapter7Entry15PartialSum (r : ℂ) (x : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ Icc 1 N, chapter7Entry15Term r x k

/-- The exponential `exp (2 * π * x * I)` whose powers bound sine partial sums. -/
private noncomputable def sinExp (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- Uniform bound for sine partial sums at `x`: `2 / ‖sinExp x - 1‖`. -/
private noncomputable def sinBound (x : ℝ) : ℝ :=
  2 / ‖sinExp x - 1‖

/-- Sine partial sums: `∑ j ∈ range k, sin (2 * π * x * j)`. -/
private noncomputable def bpA (x : ℝ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range k, ((((Real.sin (2 * Real.pi * x * j) : ℝ))) : ℂ)

/-- Inverse-power factor `k ^ (-s)` for the summation by parts. -/
private noncomputable def bpG (s : ℂ) (k : ℕ) : ℂ :=
  ((((k : ℝ))) : ℂ) ^ (-s)

/-- Summation-by-parts summand `A_{i+1} * (g_{i+1} - g_i)`. -/
private noncomputable def bpH (x : ℝ) (s : ℂ) (i : ℕ) : ℂ :=
  bpA x (i + 1) * (bpG s (i + 1) - bpG s i)

/-- The absolutely convergent by-parts series, whose negation is the sine sum. -/
private noncomputable def bpT (x : ℝ) (s : ℂ) : ℂ :=
  ∑' i, bpH x s i
end
end Entry15Vonstaudtclausen
end MathlibExt.Analysis.Ramanujan.Part1Ch7
