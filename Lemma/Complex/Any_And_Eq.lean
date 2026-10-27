import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Complex_exists_differentiable_eqOn_halfPlane_of_forall_exists_entire_mul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Complex_exists_differentiable_eqOn_halfPlane_of_forall_exists_entire_mul_eq.lean)
-/
@[path]
private lemma main
  {L : ℂ → ℂ}
  {σ : ℝ}
  -- given
  (hL : ContinuousOn L {s : ℂ | σ < s.re})
  (h : ∀ s₁ : ℂ, ∃ (Z E : ℂ → ℂ) (c : ℂ) (σ' : ℝ), Differentiable ℂ Z ∧ Differentiable ℂ E ∧ c ≠ 0 ∧ E s₁ ≠ 0 ∧ ∀ s : ℂ, σ' < s.re → Z s = c * E s * L s) :
  -- imply
  ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ ∃ σ'' : ℝ, ∀ s : ℂ, σ'' < s.re → Λ s = L s := by
  -- proof
  classical
  choose Z E c σ' hZ hE hc hE1 hid using h
  have hZa : ∀ p, AnalyticOnNhd ℂ (Z p) Set.univ := fun p => Iff.mpr Complex.analyticOnNhd_univ_iff_differentiable (hZ p)
  have hEa : ∀ p, AnalyticOnNhd ℂ (E p) Set.univ := fun p => Iff.mpr Complex.analyticOnNhd_univ_iff_differentiable (hE p)
  have hopen : ∀ a : ℝ, IsOpen {s : ℂ | a < s.re} := fun a => isOpen_lt continuous_const Complex.continuous_re
  have star : ∀ p q s, c q * E q s * Z p s = c p * E p s * Z q s := by
    intro p q
    have h1 : AnalyticOnNhd ℂ (fun s => c q * E q s * Z p s) Set.univ := ((analyticOnNhd_const.mul (hEa q)).mul (hZa p))
    have h2 : AnalyticOnNhd ℂ (fun s => c p * E p s * Z q s) Set.univ := ((analyticOnNhd_const.mul (hEa p)).mul (hZa q))
    set z₀ : ℂ := ((max (σ' p) (σ' q) + 1 : ℝ) : ℂ) with hz₀
    have hev : (fun s => c q * E q s * Z p s) =ᶠ[nhds z₀] (fun s => c p * E p s * Z q s) := by
      have hm : {s : ℂ | max (σ' p) (σ' q) < s.re} ∈ nhds z₀ := by
        apply (hopen _).mem_nhds
        show max (σ' p) (σ' q) < z₀.re
        rw [hz₀, Complex.ofReal_re]
        linarith
      filter_upwards [hm] with s hs
      have hsp : σ' p < s.re := lt_of_le_of_lt (le_max_left _ _) hs
      have hsq : σ' q < s.re := lt_of_le_of_lt (le_max_right _ _) hs
      rw [hid p s hsp, hid q s hsq]
      ring
    intro s
    apply h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_univ (Set.mem_univ z₀) hev (Set.mem_univ s)
  have hEne : ∀ p s, ∀ᶠ z in nhdsWithin s {s}ᶜ, E p z ≠ 0 := by
    intro p s
    obtain h0 | h0 := (hEa p s (Set.mem_univ s)).eventually_eq_zero_or_eventually_ne_zero
    ·
      exfalso
      apply hE1 p (((hEa p).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ s) h0) (Set.mem_univ p))
    · apply h0
  refine ⟨fun s => Z s s / (c s * E s s), ?_, max σ (σ' 0), ?_⟩
  ·
    intro p
    have hne : ∀ᶠ q in nhds p, E p q ≠ 0 := (hE p).continuous.continuousAt.eventually_ne (hE1 p)
    apply DifferentiableAt.congr_of_eventuallyEq
    · apply ((hZ p) p).div ((differentiableAt_const _).mul ((hE p) p)) (mul_ne_zero (hc p) (hE1 p))
    ·
      filter_upwards [hne] with q hq
      rw [div_eq_div_iff (mul_ne_zero (hc q) (hE1 q)) (mul_ne_zero (hc p) hq)]
      linear_combination -(star p q q)
  ·
    intro s hs
    have hsσ : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    apply tendsto_nhds_unique_of_eventuallyEq
    ·
      apply Filter.Tendsto.mono_left
      ·
        apply ContinuousAt.tendsto
        apply DifferentiableAt.continuousAt
        apply DifferentiableAt.congr_of_eventuallyEq
        · apply ((hZ s) s).div ((differentiableAt_const _).mul ((hE s) s)) (mul_ne_zero (hc s) (hE1 s))
        ·
          have hne : ∀ᶠ q in nhds s, E s q ≠ 0 := (hE s).continuous.continuousAt.eventually_ne (hE1 s)
          filter_upwards [hne] with q hq
          rw [div_eq_div_iff (mul_ne_zero (hc q) (hE1 q)) (mul_ne_zero (hc s) hq)]
          linear_combination -(star s q q)
      · apply nhdsWithin_le_nhds
    ·
      have hH : {z : ℂ | σ < z.re} ∈ nhdsWithin s {s}ᶜ := mem_nhdsWithin_of_mem_nhds ((hopen σ).mem_nhds hsσ)
      have hcw : ContinuousWithinAt L {z : ℂ | σ < z.re} s := hL s hsσ
      have htend := hcw.tendsto.mono_left (nhdsWithin_mono s (Set.inter_subset_left (t := {s}ᶜ)))
      rwa [nhdsWithin_inter_of_mem hH] at htend
    ·
      have hm : {z : ℂ | max σ (σ' 0) < z.re} ∈ nhdsWithin s {s}ᶜ := mem_nhdsWithin_of_mem_nhds ((hopen _).mem_nhds hs)
      filter_upwards [hEne 0 s, hm] with z hz hzre
      have hz0 : σ' 0 < z.re := lt_of_le_of_lt (le_max_right _ _) hzre
      rw [div_eq_iff (mul_ne_zero (hc z) (hE1 z))]
      have h2 := hid 0 z hz0
      have hne0 : c 0 * E 0 z ≠ 0 := mul_ne_zero (hc 0) hz
      have : Z z z = c z * E z z * L z := by
        apply mul_left_cancel₀ hne0
        calc
          _ = c z * E z z * Z 0 z := star z 0 z
          _ = c z * E z z * (c 0 * E 0 z * L z) := by rw [h2]
          _ = c 0 * E 0 z * (c z * E z z * L z) := by ring
      rw [this]
      ring


-- created on 2026-10-20
