/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry15Vonstaudtclausen.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.ZMod
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Def.Analysis.Ramanujan.Part1Ch7Phi
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.Complex.SummableUniformlyOn
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

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
noncomputable def sinExp (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- Uniform bound for sine partial sums at `x`: `2 / ‖sinExp x - 1‖`. -/
noncomputable def sinBound (x : ℝ) : ℝ :=
  2 / ‖sinExp x - 1‖

/-- Sine partial sums: `∑ j ∈ range k, sin (2 * π * x * j)`. -/
noncomputable def bpA (x : ℝ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range k, ((((Real.sin (2 * Real.pi * x * j) : ℝ))) : ℂ)

/-- Inverse-power factor `k ^ (-s)` for the summation by parts. -/
noncomputable def bpG (s : ℂ) (k : ℕ) : ℂ :=
  ((((k : ℝ))) : ℂ) ^ (-s)

/-- Summation-by-parts summand `A_{i+1} * (g_{i+1} - g_i)`. -/
noncomputable def bpH (x : ℝ) (s : ℂ) (i : ℕ) : ℂ :=
  bpA x (i + 1) * (bpG s (i + 1) - bpG s i)

/-- The absolutely convergent by-parts series, whose negation is the sine sum. -/
noncomputable def bpT (x : ℝ) (s : ℂ) : ℂ :=
  ∑' i, bpH x s i

end
end Entry15Vonstaudtclausen
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
