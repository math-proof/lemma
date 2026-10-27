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
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry24Dougall.Part2
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry24Dougall

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem continuousOn_cLi2 : ContinuousOn cLi2 (Metric.closedBall 0 1) := by
  have hf : ∀ j : ℕ, ContinuousOn (fun z : ℂ => cLi2Term z j)
      (Metric.closedBall 0 1) := by
    intro j
    have hc : Continuous (fun z : ℂ => z ^ (j + 1) / ((((j + 1 : ℕ)) : ℂ) ^ 2)) :=
      (continuous_id.pow (j + 1)).div_const _
    have heq : (fun z : ℂ => cLi2Term z j)
        = (fun z : ℂ => z ^ (j + 1) / ((((j + 1 : ℕ)) : ℂ) ^ 2)) := rfl
    rw [heq]
    exact hc.continuousOn
  have hbound : ∀ (j : ℕ) (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 1 →
      ‖cLi2Term z j‖ ≤ (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    intro j z hz
    have hnorm : ‖z‖ ≤ 1 := by
      have hdist : dist z (0 : ℂ) ≤ 1 := Metric.mem_closedBall.mp hz
      rwa [dist_eq_norm, sub_zero] at hdist
    have hnum : ‖z‖ ^ (j + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hnorm
    have hDpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by positivity
    have hD' : ‖((((j + 1 : ℕ)) : ℂ) ^ 2)‖ = ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
      rw [norm_pow, Complex.norm_natCast]
    have hterm : ‖cLi2Term z j‖ = ‖z‖ ^ (j + 1) / ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
      unfold cLi2Term
      rw [norm_div, norm_pow, hD']
    rw [hterm]
    exact div_le_div_of_nonneg_right hnum (le_of_lt hDpos)
  have hcont := continuousOn_tsum hf summable_inv_succ_sq hbound
  have heq : (fun x : ℂ => ∑' n, cLi2Term x n) = cLi2 := rfl
  rw [heq] at hcont
  exact hcont

theorem cLi2_zero : cLi2 0 = 0 := by
  have hfun : (fun j : ℕ => cLi2Term (0 : ℂ) j) = fun _ => 0 := by
    funext j
    unfold cLi2Term
    simp only [zero_pow (Nat.succ_ne_zero j), zero_div]
  unfold cLi2
  rw [hfun]
  exact tsum_zero

theorem hasSum_real_succ_sq :
    HasSum (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2))
      (Real.pi ^ 2 / 6) := by
  have hcorr : ∑ i ∈ Finset.range 1, (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) i = 0 := by
    simp
  have h2 : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2))
      (Real.pi ^ 2 / 6 +
        ∑ i ∈ Finset.range 1, (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) i) := by
    rw [hcorr, add_zero]
    exact hasSum_zeta_two
  exact (hasSum_nat_add_iff 1).mpr h2

theorem cLi2_one : cLi2 1 = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := by
  have hbase := hasSum_real_succ_sq
  have hc : HasSum (fun j : ℕ => (((1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2) : ℝ) : ℂ))
      (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) :=
    (Complex.hasSum_ofReal).mpr hbase
  have hfun : (fun j : ℕ => cLi2Term (1 : ℂ) j)
      = (fun j : ℕ => (((1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2) : ℝ) : ℂ)) := by
    funext j
    unfold cLi2Term
    simp only [one_pow]
    have hD : ((((j + 1 : ℕ)) : ℂ) ^ 2)
        = ((((((j + 1 : ℕ)) : ℝ) ^ 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hD, ← Complex.ofReal_one, ← Complex.ofReal_div]
  rw [← hfun] at hc
  unfold cLi2
  exact hc.tsum_eq

theorem hasDerivAt_cLi2Term (j : ℕ) (y : ℂ) :
    HasDerivAt (fun z : ℂ => cLi2Term z j) (cLi2DerivTerm y j) y := by
  have hj : ((((j + 1 : ℕ)) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero j
  have hpow := hasDerivAt_pow (j + 1) y
  simp only [Nat.add_sub_cancel] at hpow
  have hdiv := hpow.div_const ((((j + 1 : ℕ)) : ℂ) ^ 2)
  have heq : ((((j + 1 : ℕ)) : ℂ) * y ^ j) / ((((j + 1 : ℕ)) : ℂ) ^ 2)
      = cLi2DerivTerm y j := by
    unfold cLi2DerivTerm
    field_simp
  rw [heq] at hdiv
  have hfun : (fun z : ℂ => cLi2Term z j)
      = (fun z : ℂ => z ^ (j + 1) / ((((j + 1 : ℕ)) : ℂ) ^ 2)) := rfl
  rw [hfun]
  exact hdiv

theorem norm_cLi2DerivTerm_le (r : ℝ) (j : ℕ) (y : ℂ) (hy : ‖y‖ < r) :
    ‖cLi2DerivTerm y j‖ ≤ r ^ j := by
  unfold cLi2DerivTerm
  have hD : ‖((((j + 1 : ℕ)) : ℂ))‖ = ((((j + 1 : ℕ)) : ℝ)) := Complex.norm_natCast _
  have h1 : (1 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ)) := by
    have hj : (1 : ℕ) ≤ j + 1 := Nat.le_add_left 1 j
    exact_mod_cast hj
  have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ)) := lt_of_lt_of_le zero_lt_one h1
  rw [norm_div, norm_pow, hD]
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg _) (le_of_lt hy)
  have hpow : ‖y‖ ^ j ≤ r ^ j :=
    pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hy) j
  calc ‖y‖ ^ j / ((((j + 1 : ℕ)) : ℝ))
      ≤ r ^ j / ((((j + 1 : ℕ)) : ℝ)) :=
        div_le_div_of_nonneg_right hpow (le_of_lt hpos)
    _ ≤ r ^ j := div_le_self (pow_nonneg hr0 _) h1

theorem hasDerivAt_cLi2 {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt cLi2 (cLi2Deriv z) z := by
  set r : ℝ := (1 + ‖z‖) / 2 with hr
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hr0 : 0 < r := by
    rw [hr]
    linarith
  have hzr : ‖z‖ < r := by
    rw [hr]
    linarith
  have hr1 : r < 1 := by
    rw [hr]
    linarith
  have hu : Summable (fun j : ℕ => r ^ j) :=
    summable_geometric_of_lt_one (le_of_lt hr0) hr1
  have ht : IsOpen (Metric.ball (0 : ℂ) r) := Metric.isOpen_ball
  have hprec : IsPreconnected (Metric.ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).isPreconnected
  have hg : ∀ (j : ℕ) (y : ℂ), y ∈ Metric.ball (0 : ℂ) r →
      HasDerivAt (fun z : ℂ => cLi2Term z j) (cLi2DerivTerm y j) y := by
    intro j y _
    exact hasDerivAt_cLi2Term j y
  have hg' : ∀ (j : ℕ) (y : ℂ), y ∈ Metric.ball (0 : ℂ) r →
      ‖cLi2DerivTerm y j‖ ≤ r ^ j := by
    intro j y hy
    have hnorm : ‖y‖ < r := by
      have hdist : dist y (0 : ℂ) < r := Metric.mem_ball.mp hy
      rwa [dist_eq_norm, sub_zero] at hdist
    exact norm_cLi2DerivTerm_le r j y hnorm
  have hy0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_self]
    exact hr0
  have hg0 : Summable (fun j : ℕ => cLi2Term (0 : ℂ) j) := by
    have hfun : (fun j : ℕ => cLi2Term (0 : ℂ) j) = fun _ => 0 := by
      funext j
      unfold cLi2Term
      simp only [zero_pow (Nat.succ_ne_zero j), zero_div]
    rw [hfun]
    exact summable_zero
  have hy : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact hzr
  have hmain := hasDerivAt_tsum_of_isPreconnected (u := fun j : ℕ => r ^ j)
    (t := Metric.ball (0 : ℂ) r) (y₀ := (0 : ℂ)) (y := z)
    hu ht hprec hg hg' hy0 hg0 hy
  have heq1 : (fun z : ℂ => ∑' n, cLi2Term z n) = cLi2 := rfl
  have heq2 : (∑' n, cLi2DerivTerm z n) = cLi2Deriv z := rfl
  rw [heq1, heq2] at hmain
  exact hmain

theorem summable_cLi2Deriv {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun j : ℕ => cLi2DerivTerm z j) := by
  set r : ℝ := (1 + ‖z‖) / 2 with hr
  have hzr : ‖z‖ < r := by
    rw [hr]
    linarith [norm_nonneg z, hz]
  have hr1 : r < 1 := by
    rw [hr]
    linarith [hz]
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg _) (le_of_lt hzr)
  have hu : Summable (fun j : ℕ => r ^ j) :=
    summable_geometric_of_lt_one hr0 hr1
  exact Summable.of_norm_bounded hu (fun j => norm_cLi2DerivTerm_le r j z hzr)

theorem mul_cLi2Deriv {z : ℂ} (hz : ‖z‖ < 1) :
    z * cLi2Deriv z = -Complex.log (1 - z) := by
  have hsumm := summable_cLi2Deriv hz
  have hlog := Complex.hasSum_taylorSeries_neg_log' hz
  have hcast : ∀ n : ℕ, ((((n + 1 : ℕ)) : ℂ)) = ((n : ℂ) + 1) := by
    intro n
    push_cast
    ring
  have hlog2 : HasSum (fun n : ℕ => z ^ (n + 1) / ((((n + 1 : ℕ)) : ℂ)))
      (-Complex.log (1 - z)) := by
    have hfun : (fun n : ℕ => z ^ (n + 1) / ((((n + 1 : ℕ)) : ℂ)))
        = (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1)) := by
      funext n
      rw [hcast]
    rw [hfun]
    convert hlog using 2
  have hmul : z * cLi2Deriv z
      = ∑' j, z ^ (j + 1) / ((((j + 1 : ℕ)) : ℂ)) := by
    unfold cLi2Deriv
    rw [← hsumm.tsum_mul_left z]
    refine tsum_congr fun j => ?_
    unfold cLi2DerivTerm
    rw [← mul_div_assoc, ← pow_succ']
  rw [hmul]
  exact hlog2.tsum_eq

end
end Entry24Dougall
end Ramanujan.Part1Ch9
end
