/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.ArcsinTaylorSeries
import Lemma.Real.ArcsinTaylorSeries
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry16Tanseries

open MathlibExt.Analysis.SpecialFunctions.ArcsinTaylorSeries

open scoped BigOperators

noncomputable section

def chapter9CentralSineTerm (x : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose (2 * k) k : ℝ) * Real.sin x ^ (2 * k + 1) /
    ((2 : ℝ) ^ (2 * k) * (((2 * k + 1 : ℕ) : ℝ) ^ 2))

/-- Summand of the Entry 16 tan-series (difference of the cosine and sine
central terms). Named `Entry18` in the wishlist formalization; renamed here since
the recorded provenance (`WantedExt/Sources/AnalysisCore.md`) attributes both the
tan formula and this series to Entry 16, and no Entry 18 formalization exists. -/
def chapter9Entry16DifferenceTerm (x : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose (2 * k) k : ℝ) *
      (Real.cos x ^ (2 * k + 1) - Real.sin x ^ (2 * k + 1)) /
    ((2 : ℝ) ^ (2 * k) * (((2 * k + 1 : ℕ) : ℝ) ^ 2))

def chap9H (x : ℝ) : ℝ :=
  arcsinIntegralSeries (Real.cos x) - arcsinIntegralSeries (Real.sin x) +
    (1 / 2 : ℝ) * arcsinIntegralSeries (Real.sin (2 * x)) -
      (Real.pi / 2) * Real.log (2 * Real.cos x)

def chap9D (θ : ℝ) : ℝ := Real.cos θ / Real.sinc θ

def chap9Phi (θ : ℝ) : ℝ := arcsinIntegralSeries (Real.sin θ)

def chap9A (θ : ℝ) : ℝ := θ * Real.log (Real.sin θ)

end
end Entry16Tanseries
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
