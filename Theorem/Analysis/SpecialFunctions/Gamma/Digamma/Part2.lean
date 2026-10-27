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
import Def.Analysis.SpecialFunctions.Gamma.Digamma.Part2
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

theorem helper_seriesDomain_open : IsOpen seriesDomain := by
  have heq : seriesDomain = Complex.re ⁻¹' Set.Ioi 1 := rfl
  rw [heq]
  exact isOpen_Ioi.preimage Complex.continuous_re

theorem helper_seriesDomain_convex : Convex ℝ seriesDomain :=
  convex_halfSpace_gt
    (LinearMap.isLinearMap_of_compatibleSMul ℝ Complex.reLm) 1

theorem helper_seriesDomain_preconn : IsPreconnected seriesDomain :=
  helper_seriesDomain_convex.isPreconnected

theorem helper_seriesTerm_re (j : ℕ) (s : ℂ)
    (hs : s ∈ seriesDomain) :
    (j : ℝ) + 1 ≤ ((j : ℂ) + s).re := by
  rw [Complex.add_re, Complex.natCast_re]
  have hs' : (1 : ℝ) < s.re := hs
  linarith

theorem helper_seriesTerm_ne (j : ℕ) (s : ℂ)
    (hs : s ∈ seriesDomain) : (j : ℂ) + s ≠ 0 := by
  have hpos : (0 : ℝ) < ((j : ℂ) + s).re := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hle := helper_seriesTerm_re j s hs
    linarith
  intro hcon
  have h0 := congrArg Complex.re hcon
  rw [Complex.zero_re] at h0
  linarith

theorem helper_seriesTerm_hasDeriv (j : ℕ) (s : ℂ)
    (hs : s ∈ seriesDomain) :
    HasDerivAt (digammaSeriesTerm j) (1 / ((j : ℂ) + s) ^ 2) s := by
  have hne : s + (j : ℂ) ≠ 0 := by
    have h := helper_seriesTerm_ne j s hs
    rwa [add_comm] at h
  have hbase : HasDerivAt (fun t : ℂ => t + (j : ℂ)) 1 s :=
    (hasDerivAt_id' s).add_const ((j : ℂ))
  have hinv := hbase.inv hne
  have hsub := HasDerivAt.const_sub (1 / ((j : ℂ) + 1)) hinv
  simp only [Pi.inv_apply] at hsub
  have hfun : digammaSeriesTerm j
      = fun t : ℂ => 1 / ((j : ℂ) + 1) - (t + (j : ℂ))⁻¹ := by
    funext t
    simp [digammaSeriesTerm, one_div, add_comm]
  have hderiv : -(-1 / (s + (j : ℂ)) ^ 2)
      = 1 / ((j : ℂ) + s) ^ 2 := by
    rw [add_comm s ((j : ℂ))]
    ring
  rw [hfun, ← hderiv]
  exact hsub

theorem helper_seriesDeriv_bound (j : ℕ) (s : ℂ)
    (hs : s ∈ seriesDomain) :
    ‖(1 / ((j : ℂ) + s) ^ 2 : ℂ)‖ ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
  have hnorm : ((j : ℝ) + 1) ≤ ‖((j : ℂ) + s)‖ :=
    (helper_seriesTerm_re j s hs).trans
      ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hsq : ((j : ℝ) + 1) ^ 2 ≤ ‖((j : ℂ) + s)‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hnorm 2
  rw [norm_div, norm_one, norm_pow]
  exact one_div_le_one_div_of_le (by positivity) hsq

theorem helper_series_summable_at_two :
    Summable (fun j : ℕ => digammaSeriesTerm j 2) := by
  refine Summable.of_norm_bounded Real.summable_one_div_add_nat_succ_sq
    (fun j => ?_)
  have e1 : ((j : ℂ) + 1) = Complex.ofReal ((j : ℝ) + 1) := by
    simp [Complex.ofReal_add]
  have e2 : ((j : ℂ) + 2) = Complex.ofReal ((j : ℝ) + 2) := by
    simp [Complex.ofReal_add]
  have h1 : ((j : ℂ) + 1) ≠ 0 := by
    rw [e1]
    exact_mod_cast ne_of_gt (show (0 : ℝ) < (j : ℝ) + 1 by positivity)
  have h2 : ((j : ℂ) + 2) ≠ 0 := by
    rw [e2]
    exact_mod_cast ne_of_gt (show (0 : ℝ) < (j : ℝ) + 2 by positivity)
  have heq : digammaSeriesTerm j 2
      = 1 / (((j : ℂ) + 1) * ((j : ℂ) + 2)) := by
    simp only [digammaSeriesTerm, div_sub_div _ _ h1 h2, one_mul, mul_one]
    have hnum : ((j : ℂ) + 2) - ((j : ℂ) + 1) = 1 := by ring
    rw [hnum]
  rw [heq, norm_div, norm_one]
  have hle : ((j : ℝ) + 1) ^ 2
      ≤ ‖((j : ℂ) + 1) * ((j : ℂ) + 2)‖ := by
    rw [norm_mul, e1, e2, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity),
      abs_of_nonneg (show (0 : ℝ) ≤ (j : ℝ) + 2 by positivity)]
    have h2le : (j : ℝ) + 1 ≤ (j : ℝ) + 2 := by linarith
    calc ((j : ℝ) + 1) ^ 2 = ((j : ℝ) + 1) * ((j : ℝ) + 1) := by ring
      _ ≤ ((j : ℝ) + 1) * ((j : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left h2le (by positivity)
  exact one_div_le_one_div_of_le (by positivity) hle

theorem helper_seriesFun_hasDeriv (s : ℂ)
    (hs : s ∈ seriesDomain) :
    HasDerivAt digammaSeriesFun
      (∑' j : ℕ, (1 / ((j : ℂ) + s) ^ 2 : ℂ)) s :=
  hasDerivAt_tsum_of_isPreconnected Real.summable_one_div_add_nat_succ_sq
    helper_seriesDomain_open helper_seriesDomain_preconn
    (fun j y hy => helper_seriesTerm_hasDeriv j y hy)
    (fun j y hy => helper_seriesDeriv_bound j y hy)
    (by
      change (1 : ℝ) < (2 : ℂ).re
      have h2c : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
      rw [h2c, Complex.ofReal_re]
      norm_num)
    helper_series_summable_at_two hs

theorem helper_seriesFun_analytic :
    AnalyticOnNhd ℂ digammaSeriesFun seriesDomain :=
  DifferentiableOn.analyticOnNhd
    (fun s hs =>
      (helper_seriesFun_hasDeriv s hs).differentiableAt.differentiableWithinAt)
    helper_seriesDomain_open

end Complex
end
