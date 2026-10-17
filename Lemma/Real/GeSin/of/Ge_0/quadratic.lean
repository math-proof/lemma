import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.Compact
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  (h₀ : 0 ≤ x) :
-- imply
  Real.sin x ≥ x * (1 - x / Real.pi) := by
-- proof
  let φ : ℝ → ℝ := fun t => Real.sin t - t * (1 - t / Real.pi)
  have hHas (t : ℝ) : HasDerivAt φ (Real.cos t - 1 + 2 * t / Real.pi) t := by
    have hv0 := ((hasDerivAt_id t).const_mul Real.pi⁻¹).const_sub (1 : ℝ)
    have hv : HasDerivAt (fun u => (1 : ℝ) - u / Real.pi) (-(Real.pi⁻¹ * 1)) t :=
      hv0.congr_of_eventuallyEq <| by
        filter_upwards with u
        simp
        ring_nf
    have hmul := (hasDerivAt_id t).mul hv
    have hsub := (Real.hasDerivAt_sin t).sub hmul
    refine (hsub.congr_of_eventuallyEq ?_).congr_deriv ?_
    ·
      filter_upwards with u
      simp [φ]
    ·
      field_simp
      simp [id]
      ring
  have hderiv (t : ℝ) : deriv φ t = Real.cos t - 1 + 2 * t / Real.pi := (hHas t).deriv
  have hcont : Continuous φ :=
    continuous_iff_continuousAt.mpr fun t => (hHas t).continuousAt
  have hφ0 : φ 0 = 0 := by
    simp [φ]
  have hφpi : φ Real.pi = 0 := by
    simp [φ, Real.sin_pi]
  if hle : x ≤ Real.pi then
    by_contra hlt
    have hxI : x ∈ Set.Icc (0 : ℝ) Real.pi := ⟨h₀, hle⟩
    have hlt' : φ x < 0 := by
      simpa [φ] using hlt
    obtain ⟨y, hy, hmin⟩ :=
      (isCompact_Icc (a := (0 : ℝ)) (b := Real.pi)).exists_isMinOn
        (Set.nonempty_Icc.mpr (h₀.trans hle)) hcont.continuousOn
    have hyneg : φ y < 0 := lt_of_le_of_lt (hmin hxI) hlt'
    have hyne0 : y ≠ 0 := by
      rintro rfl
      linarith [hφ0]
    have hynepi : y ≠ Real.pi := by
      rintro rfl
      linarith [hφpi]
    have hyoo1 : (0 : ℝ) < y := hy.1.lt_of_ne (Ne.symm hyne0)
    have hyoo2 : y < Real.pi := hy.2.lt_of_ne hynepi
    have hloc : IsLocalMin φ y := hmin.isLocalMin (Icc_mem_nhds hyoo1 hyoo2)
    have hder0 : deriv φ y = 0 := hloc.deriv_eq_zero
    rw [hderiv] at hder0
    have hcos : Real.cos y = 1 - 2 * y / Real.pi := by
      linarith
    have hsin2 : Real.sin y ^ 2 = 4 * y * (Real.pi - y) / Real.pi ^ 2 := by
      have hsq : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
      rw [hcos] at hsq
      field_simp at hsq ⊢
      nlinarith
    have hsinlt : Real.sin y < y * (Real.pi - y) / Real.pi := by
      simp only [φ] at hyneg
      field_simp at hyneg ⊢
      linarith
    have hsin_nn : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2
    have hrhs_nn : 0 ≤ y * (Real.pi - y) / Real.pi := by
      positivity
    have hsqlt : Real.sin y ^ 2 < (y * (Real.pi - y) / Real.pi) ^ 2 :=
      (sq_lt_sq₀ hsin_nn hrhs_nn).2 hsinlt
    rw [hsin2] at hsqlt
    have h4 : (4 : ℝ) < y * (Real.pi - y) := by
      field_simp at hsqlt
      nlinarith [hsqlt, hyoo1, sub_pos.mpr hyoo2, Real.pi_pos]
    have hmax : y * (Real.pi - y) ≤ Real.pi ^ 2 / 4 := by
      nlinarith [sq_nonneg (y - Real.pi / 2)]
    have hpi : Real.pi ^ 2 / 4 < 4 := by
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    linarith
  else
    have hge : Real.pi ≤ x := le_of_not_ge hle
    have hmono : MonotoneOn φ (Set.Ici Real.pi) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici _) hcont.continuousOn ?_ ?_
      ·
        intro t ht
        exact (hHas t).differentiableAt.differentiableWithinAt
      ·
        intro t ht
        rw [hderiv]
        field_simp
        have ht' : Real.pi < t := by
          simpa [interior_Ici] using ht
        nlinarith [Real.neg_one_le_cos t, ht', Real.pi_pos]
    have hleφ : φ Real.pi ≤ φ x := hmono (by simp) (by simpa using hge) hge
    have : 0 ≤ φ x := by
      simpa [hφpi] using hleφ
    simpa [φ] using this


-- created on 2026-10-11
-- updated on 2026-10-17
