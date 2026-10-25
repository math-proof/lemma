/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry16PsiSeries.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lemma.Nat.Ramanujan.Part1Ch3Entry12SummableSuccN
import Def.NumberTheory.Ramanujan.Part1Ch3Entry16Corollary1JensenSeries
import Lemma.Nat.Ramanujan.Part1Ch3Entry16Corollary1JensenSeries
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
