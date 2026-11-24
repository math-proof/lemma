module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.NumberTheory.Ramanujan.Part1Ch3Entry16Corollary1JensenSeries
public import Theorem.Nat.Ramanujan.Part1Ch3Entry16Corollary1JensenSeries


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry16PsiSeries.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/
/-!
# Ramanujan's psi-series identity

This file proves Berndt's formulas (16.4)-(16.5) for Ramanujan's recursively defined
psi-polynomials and their associated exponential series.
-/
namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry16PsiSeries

def psi : ℕ → ℕ → ℂ → ℂ
  | 0, 1, _ => 1
  | 0, _, _ => 0
  | r + 1, k, n =>
      (n - (↑(r + 1) : ℂ) - (↑k : ℂ) + 1) * psi r k n +
        ((↑(r + 1) : ℂ) + (↑k : ℂ) - 2) * if k = 0 then 0 else psi r (k - 1) n

noncomputable def e16ps_term (r : ℕ) (n u : ℂ) (j : ℕ) : ℂ :=
  (n + (j : ℂ)) ^ (r + j) * Complex.exp (-u * (n + (j : ℂ))) * u ^ j /
    (Nat.factorial j : ℂ)

noncomputable def e16ps_G (r : ℕ) (n u : ℂ) : ℂ :=
  ∑' j : ℕ, e16ps_term r n u j

noncomputable def e16ps_P (r : ℕ) (n u : ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 (r + 1), psi r k n / (1 - u) ^ (r + k)

def e16ps_D : Set ℂ :=
  {u | ‖u * Complex.exp (1 - u)‖ < 1 ∧ ‖u‖ < 1}

noncomputable def e16ps_q (u : ℂ) : ℝ :=
  ‖u * Complex.exp (-u)‖

end Entry16PsiSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
