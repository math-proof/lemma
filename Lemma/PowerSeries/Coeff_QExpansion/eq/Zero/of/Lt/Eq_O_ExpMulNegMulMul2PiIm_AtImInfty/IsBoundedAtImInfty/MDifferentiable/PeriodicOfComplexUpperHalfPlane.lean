import Mathlib
import Initialize.Tactic.Attr.Basic
open UpperHalfPlane Filter Asymptotics Function
open scoped Real Topology Manifold


private lemma norm_integrand_le (f : ℍ → ℂ) (n : ℕ) {C L t A : ℝ} (ht : 0 < t) (hAt : A ≤ t)
  (hC : ∀ z : ℍ, A ≤ z.im → ‖f z‖ ≤ C * ‖Real.exp (-(2 * Real.pi * L) * z.im)‖) (u : ℝ) :
  ‖1 / Periodic.qParam 1 (u + t * (UpperHalfPlane.I : ℂ)) ^ n *
      f ⟨u + t * (UpperHalfPlane.I : ℂ), by simpa using ht⟩‖ ≤
    max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t) := by
  set τ : ℍ := ⟨u + t * (UpperHalfPlane.I : ℂ), by simpa using ht⟩ with hτ
  have hI : (u + t * (UpperHalfPlane.I : ℂ)).im = t := by simp [UpperHalfPlane.I]
  have him : τ.im = t := by rwa [hτ]
  rw [norm_mul, norm_div, norm_one, norm_pow, Periodic.norm_qParam]
  have h1 : (1 : ℝ) / Real.exp (-2 * Real.pi * (u + t * (UpperHalfPlane.I : ℂ)).im / 1) ^ n =
      Real.exp (2 * Real.pi * n * t) := by
    rw [hI, div_one, ← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    congr 1; ring
  rw [h1]
  have h2 : ‖f τ‖ ≤ max C 0 * Real.exp (-(2 * Real.pi * L) * t) := by
    have := hC τ (him ▸ hAt)
    rw [him, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  calc
    _ ≤ Real.exp (2 * Real.pi * n * t) * (max C 0 * Real.exp (-(2 * Real.pi * L) * t)) :=
      mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t) := by
      rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

private lemma helper_main (f : ℍ → ℂ)
  (hper : Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ))
  (hhol : MDifferentiable 𝓘ℂ 𝓘(ℂ) f) (hbdd : IsBoundedAtImInfty f)
  (L : ℝ) (hO : f =O[atImInfty] fun τ : ℍ => Real.exp (-(2 * Real.pi * L) * τ.im))
  (n : ℕ) (hn : (n : ℝ) < L) :
  PowerSeries.coeff n (qExpansion 1 f) = 0 := by
  obtain ⟨C, hC⟩ := hO.bound
  rw [Filter.Eventually, atImInfty_mem] at hC
  obtain ⟨A, hA⟩ := hC
  set a : ℂ := PowerSeries.coeff n (qExpansion 1 f) with ha
  have hbound : ∀ t : ℝ, max A 1 ≤ t →
      ‖a‖ ≤ max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t) := by
    intro t hAt
    have ht : 0 < t := lt_of_lt_of_le one_pos ((le_max_right A 1).trans hAt)
    have hint := qExpansion_coeff_eq_intervalIntegral one_pos hper hhol hbdd n ht
    simp only [Complex.ofReal_one, div_one, one_mul] at hint
    rw [ha, hint]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun u : ℝ => 1 / Periodic.qParam 1 (u + t * (UpperHalfPlane.I : ℂ)) ^ n *
        f ⟨u + t * (UpperHalfPlane.I : ℂ), by simpa using ht⟩)
      (C := max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t))
      (fun u _ => norm_integrand_le f n ht ((le_max_left A 1).trans hAt) hA u)
    simpa using this
  have hlim : Tendsto (fun t : ℝ => max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t))
    atTop (𝓝 0) := by
    have hneg : 2 * Real.pi * ((n : ℝ) - L) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hn)
    have h1 : Tendsto (fun t : ℝ => Real.exp (2 * Real.pi * ((n : ℝ) - L) * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hneg)
    simpa using h1.const_mul (max C 0)
  have hle : ‖a‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨max A 1, hbound⟩)
  refine norm_le_zero_iff.mp hle

open UpperHalfPlane in
open scoped Manifold in
/--
[UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg.lean)
-/
@[path]
private lemma main
  {f : UpperHalfPlane → ℂ}
  {L : ℝ}
  {n : ℕ}
-- given
  (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ))
  (hhol : MDifferentiable 𝓘ℂ 𝓘ℂ f)
  (hbdd : UpperHalfPlane.IsBoundedAtImInfty f)
  (hO : f =O[UpperHalfPlane.atImInfty] fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * L) * τ.im))
  (hn : (n : ℝ) < L) :
-- imply
  PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f) = 0 :=
-- proof
  helper_main f hper hhol hbdd L hO n hn


-- created on 2026-10-23
