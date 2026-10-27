/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Def.Analysis.SpecialFunctions.Gamma.Digamma.Part3
open scoped Real
open Filter Finset Topology

/-!
# Series and analyticity facts for Gamma and digamma

For `x > 0`, the digamma series `∑ (1/(j+1) - 1/(x+j+1))` sums to `ψ(x+1) + γ`, where
`ψ = (log ∘ Gamma)'`, and its termwise derivative gives the trigamma series `∑ 1/(y+j+1)²`.
The file also proves that `Complex.Gamma` and `Complex.digamma` are analytic away from the
nonpositive integers, that the complex derivative of `Gamma` restricts to the real one on
`(0, ∞)`, and that `∑ 1/(z+k+1)²` converges absolutely for every complex `z` away from the
negative integers, and that for `1 < s.re` the complex digamma function satisfies
the expansion `ψ(s) + γ = ∑ j, (1/(j+1) - 1/(j+s))` (as a `HasSum` statement).
-/


noncomputable section

namespace Complex

theorem helper_digammaFun_analytic :
    AnalyticOnNhd ℂ digammaFun seriesDomain := by
  intro s hs
  have hs' : (1 : ℝ) < s.re := hs
  have hw : ∀ m : ℕ, s ≠ -((m : ℕ) : ℂ) := by
    intro m hcon
    have h0 := congrArg Complex.re hcon
    rw [Complex.neg_re, Complex.natCast_re] at h0
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  exact (Complex.analyticAt_digamma s hw).add analyticAt_const

theorem helper_series_agree_real (t : ℝ) (ht : 1 < t) :
    digammaFun (t : ℂ) = digammaSeriesFun (t : ℂ) := by
  have hx : (0 : ℝ) < t - 1 := by linarith
  have hsum := Real.hasSum_digamma_series (t - 1) hx
  rw [sub_add_cancel] at hsum
  have htsum := hsum.tsum_eq
  have hcast : ((∑' j : ℕ,
      (1 / ((j : ℝ) + 1) - 1 / ((t - 1) + (j : ℝ) + 1)) : ℝ) : ℂ)
      = digammaSeriesFun (t : ℂ) := by
    rw [Complex.ofReal_tsum]
    have hfun : (fun j : ℕ => (((1 / ((j : ℝ) + 1)
        - 1 / ((t - 1) + (j : ℝ) + 1)) : ℝ) : ℂ))
        = fun j : ℕ => digammaSeriesTerm j (t : ℂ) := by
      funext j
      have hden : Complex.ofReal ((t - 1) + (j : ℝ) + 1)
          = (j : ℂ) + (t : ℂ) := by
        push_cast
        ring
      have hden2 : Complex.ofReal ((j : ℝ) + 1) = (j : ℂ) + 1 := by
        simp [Complex.ofReal_add]
      simp only [digammaSeriesTerm, Complex.ofReal_sub, Complex.ofReal_div,
        Complex.ofReal_one, hden, hden2]
    rw [hfun]
    rfl
  have hval : ((deriv (fun u => Real.log (Real.Gamma u)) t
      + Real.eulerMascheroniConstant : ℝ) : ℂ)
      = digammaFun (t : ℂ) := by
    have ht0 : (0 : ℝ) < t := by linarith
    rw [Real.deriv_log_Gamma t ht0]
    simp only [digammaFun, Complex.digamma_def, logDeriv_apply,
      Complex.deriv_Gamma_ofReal t ht0, Complex.Gamma_ofReal,
      Complex.ofReal_div, Complex.ofReal_add]
  have htsumC := congrArg (fun r : ℝ => (r : ℂ)) htsum
  rw [hcast, hval] at htsumC
  exact htsumC.symm

theorem helper_series_freq :
    ∃ᶠ z in 𝓝[≠] (2 : ℂ), digammaFun z = digammaSeriesFun z := by
  rw [frequently_nhdsWithin_iff, frequently_nhds_iff]
  intro U hUmem hUopen
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen 2 hUmem
  set t : ℝ := 2 + min (ε / 2) (1 / 2) with htdef
  have hmin_pos : (0 : ℝ) < min (ε / 2) (1 / 2) :=
    lt_min (by linarith) (by norm_num)
  have ht2 : (2 : ℝ) < t := by rw [htdef]; linarith
  have ht1 : (1 : ℝ) < t := by linarith
  have hmin_lt : min (ε / 2) (1 / 2) < ε :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h2c : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
  have hmem : ((t : ℝ) : ℂ) ∈ Metric.ball (2 : ℂ) ε := by
    rw [Metric.mem_ball, h2c, dist_eq_norm, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - 2)]
    rw [htdef]
    linarith
  refine ⟨(t : ℂ), hball hmem, ?_, ?_⟩
  · exact helper_series_agree_real t ht1
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [h2c]
    exact_mod_cast ne_of_gt ht2

theorem helper_complex_digamma_series (s : ℂ)
    (hs : 1 < s.re) :
    Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)
      = digammaSeriesFun s := by
  have hmem2 : (2 : ℂ) ∈ seriesDomain := by
    change (1 : ℝ) < (2 : ℂ).re
    have h2c : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [h2c, Complex.ofReal_re]
    norm_num
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    helper_digammaFun_analytic helper_seriesFun_analytic
    helper_seriesDomain_preconn hmem2 helper_series_freq
  have hmem : s ∈ seriesDomain := hs
  have h := heq hmem
  simpa [digammaFun] using h

/-- The complex digamma series terms are summable for `1 < s.re`. -/
theorem summable_digammaSeriesTerm (s : ℂ) (hs : 1 < s.re) :
    Summable (fun j : ℕ => digammaSeriesTerm j s) := by
  have hmem : s ∈ seriesDomain := hs
  have hne1 : ∀ j : ℕ, ((j : ℂ) + 1) ≠ 0 := by
    intro j
    have e : ((j : ℂ) + 1) = Complex.ofReal ((j : ℝ) + 1) := by
      simp [Complex.ofReal_add]
    rw [e]
    exact_mod_cast ne_of_gt (show (0 : ℝ) < (j : ℝ) + 1 by positivity)
  have hnorm : ∀ j : ℕ, ((j : ℝ) + 1) ≤ ‖((j : ℂ) + s)‖ := fun j =>
    (helper_seriesTerm_re j s hmem).trans
      ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hterm : ∀ j : ℕ, digammaSeriesTerm j s
      = (s - 1) / (((j : ℂ) + 1) * ((j : ℂ) + s)) := by
    intro j
    rw [digammaSeriesTerm, div_sub_div _ _ (hne1 j) (helper_seriesTerm_ne j s hmem)]
    congr 1
    ring
  have hbound : ∀ j : ℕ, ‖digammaSeriesTerm j s‖
      ≤ ‖s - 1‖ / ((j : ℝ) + 1) ^ 2 := by
    intro j
    rw [hterm j, norm_div, norm_mul]
    have h1 : ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 := by
      have e : ((j : ℂ) + 1) = Complex.ofReal ((j : ℝ) + 1) := by
        simp [Complex.ofReal_add]
      rw [e, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity)]
    rw [h1]
    have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hle : ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) * ‖((j : ℂ) + s)‖ := by
      have h := hnorm j
      calc ((j : ℝ) + 1) ^ 2 = ((j : ℝ) + 1) * ((j : ℝ) + 1) := by ring
        _ ≤ ((j : ℝ) + 1) * ‖((j : ℂ) + s)‖ :=
          mul_le_mul_of_nonneg_left h (le_of_lt hpos)
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hle
  have hmaj : Summable (fun j : ℕ => ‖s - 1‖ / ((j : ℝ) + 1) ^ 2) := by
    have e : (fun j : ℕ => ‖s - 1‖ / ((j : ℝ) + 1) ^ 2)
        = fun j : ℕ => ‖s - 1‖ * (1 / ((j : ℝ) + 1) ^ 2) := by
      funext j
      ring
    rw [e]
    exact Real.summable_one_div_add_nat_succ_sq.mul_left _
  exact Summable.of_norm_bounded hmaj hbound

/-- Complex digamma expansion: for `1 < s.re`, `ψ(s) + γ` is the sum of
`1/(j+1) - 1/(j+s)`. -/
theorem hasSum_digamma_series (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun j : ℕ => digammaSeriesTerm j s)
      (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)) := by
  have hsum := summable_digammaSeriesTerm s hs
  have heq := helper_complex_digamma_series s hs
  rw [heq]
  exact hsum.hasSum

end Complex
end
