/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Filter.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Basic
import Def.Analysis.SpecialFunctions.Part1Ch9Entry19Catalangf.Part6
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry19Catalangf

open scoped Topology

open Filter

noncomputable section

theorem hasDerivAt_chap9E {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    HasDerivAt chap9E (θ * Real.cos θ / Real.sin θ) θ := by
  have habs := abs_sin_lt_one_pi_half h0 h1
  have hsin_pos : 0 < Real.sin θ := (sin_mem_Ioo_pi_half h0 h1).1
  have hsin_ne : Real.sin θ ≠ 0 := ne_of_gt hsin_pos
  have hS := hasDerivAt_chap9S habs
  have hcomp : HasDerivAt (fun θ : ℝ => ∑' k : ℕ, chap9S (Real.sin θ) k)
      ((∑' k : ℕ, chap9Sderiv (Real.sin θ) k) * Real.cos θ) θ :=
    hS.comp θ (Real.hasDerivAt_sin θ)
  have hmul := mul_tsum_Sderiv_eq_arcsin habs
  rw [arcsin_sin_eq_pi_half h0 h1] at hmul
  have hSderiv : (∑' k : ℕ, chap9Sderiv (Real.sin θ) k)
      = θ / Real.sin θ := by
    rw [eq_div_iff hsin_ne]
    linarith [hmul]
  rw [hSderiv] at hcomp
  have hval : θ / Real.sin θ * Real.cos θ = θ * Real.cos θ / Real.sin θ := by
    ring
  rw [hval] at hcomp
  exact hcomp

end
end Entry19Catalangf
end Ramanujan.Part1Ch9
end
