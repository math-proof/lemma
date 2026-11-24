module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Def.Analysis.Ramanujan.Part1Ch9Entry21Piseries2
public import Lemma.Real.Ramanujan.Part1Ch9Entry21Piseries2
public import Theorem.Real.Part1Ch9Entry32Lambertdivisor
public import Def.Analysis.Ramanujan.Part1Ch9Entry32Lambertdivisor


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry17Sec.lean -/
/-
Author: @akiezun, Avocado
-/
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/
section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry17Sec

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9XLogAbsTan (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * Real.log |Real.tan x|

def entry17Ti2 (t : ℝ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)

def entry17XG (x : ℝ) : ℝ :=
  x * Real.log x + x * Real.log (Real.sinc x) - x * Real.log (Real.cos x)

def entry17K (x : ℝ) : ℝ :=
  entry17Ti2 (Real.tan x) - chapter9XLogAbsTan x

def entry17Sr (r x : ℝ) : ℝ :=
  ∑' k : ℕ, r ^ (2 * k + 1) * Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x)
    / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)

def entry17Dr (r x : ℝ) : ℝ :=
  ∑' k : ℕ, r ^ (2 * k + 1) * 2 * Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x)
    / (((2 * k + 1 : ℕ)) : ℝ)

def entry17DrClosed (r t : ℝ) : ℝ :=
  Real.log ((1 + 2 * r * Real.cos (2 * t) + r ^ 2)
    / (1 - 2 * r * Real.cos (2 * t) + r ^ 2)) / 2

def entry17rho (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 1)

end
end Entry17Sec
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
