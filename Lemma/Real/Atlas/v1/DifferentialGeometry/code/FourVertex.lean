import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialGeometry.code.ClosedCurves
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.ClosedCurves
open MeasureTheory Real Set Filter Topology
open Real ClosedCurves


namespace SturmHurwitz

/--
[sin_half_diff_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/FourVertex.lean)
-/
@[path]
lemma sin_half_diff_ne_zero
  {t₁ t₂ : ℝ}
-- given
  (ht₁ : t₁ ∈ Ico 0 (2 * π))
  (ht₂ : t₂ ∈ Ico 0 (2 * π))
  (hne : t₁ ≠ t₂) :
-- imply
  sin ((t₁ - t₂) / 2) ≠ 0 := by
-- proof
  rw [sin_ne_zero_iff]
  intro n hn
  have hn0 : n = 0 := by
    have : (-1 : ℤ) < n := by
      by_contra h; push Not at h
      have : (n : ℝ) ≤ -1 := by exact_mod_cast h
      nlinarith [ht₁.1, ht₂.2, pi_pos]
    have : n < (1 : ℤ) := by
      by_contra h; push Not at h
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      nlinarith [ht₁.2, ht₂.1, pi_pos]
    omega
  simp [hn0] at hn; exact hne (by linarith)

end SturmHurwitz

namespace SturmHurwitz

/--
[periodic_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/FourVertex.lean)
-/
@[path]
lemma periodic_deriv
  {g : ℝ → ℝ}
-- given
  (hdiff : Differentiable ℝ g)
  (hper : ∀ t, g (t + 2 * Real.pi) = g t) :
-- imply
  ∀ t, deriv g (t + 2 * Real.pi) = deriv g t := by
-- proof
  intro t
  have lhs : HasDerivAt (fun s => g (s + 2 * π)) (deriv g (t + 2 * π)) t :=
    ((hdiff (t + 2 * π)).hasDerivAt.comp t ((hasDerivAt_id t).add_const (2 * π))).congr_deriv
      (by ring) |>.congr_of_eventuallyEq (by filter_upwards with s; simp [Function.comp])
  rw [show (fun s => g (s + 2 * π)) = g from funext hper] at lhs
  exact lhs.unique (hdiff t).hasDerivAt

end SturmHurwitz

namespace SturmHurwitz

/--
[ibp_deriv_cos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/FourVertex.lean)
-/
@[path]
lemma ibp_deriv_cos
  {g : ℝ → ℝ}
-- given
  (hdiff : Differentiable ℝ g)
  (hcont_g' : Continuous (deriv g))
  (hcont_g : Continuous g)
  (hper : ∀ t, g (t + 2 * Real.pi) = g t) :
-- imply
  ∫ t in (0:ℝ)..(2*π), deriv g t * cos t = ∫ t in (0:ℝ)..(2*π), g t * sin t := by
-- proof
  have ibp := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x _ => hdiff.differentiableAt.hasDerivAt)
    (fun (x : ℝ) _ => hasDerivAt_cos x)
    (hcont_g'.intervalIntegrable 0 (2*π))
    (continuous_sin.neg.intervalIntegrable 0 (2*π))
  simp only [cos_two_pi, cos_zero, mul_one] at ibp
  have hper0 : g (2 * π) = g 0 := by have := hper 0; simp only [zero_add] at this; exact this
  rw [hper0, sub_self] at ibp
  have hsplit : ∫ x in (0:ℝ)..(2*π), deriv g x * cos x + g x * (-sin x) =
    (∫ x in (0:ℝ)..(2*π), deriv g x * cos x) + (∫ x in (0:ℝ)..(2*π), g x * (-sin x)) :=
    intervalIntegral.integral_add
      ((hcont_g'.mul continuous_cos).intervalIntegrable 0 (2*π))
      ((hcont_g.mul continuous_sin.neg).intervalIntegrable 0 (2*π))
  have hneg : ∫ x in (0:ℝ)..(2*π), g x * (-sin x) = -(∫ x in (0:ℝ)..(2*π), g x * sin x) := by
    have : (fun x => g x * (-sin x)) = fun x => -(g x * sin x) := by ext; ring
    rw [this, intervalIntegral.integral_neg]
  linarith [hsplit, hneg]

end SturmHurwitz

namespace SturmHurwitz

/--
[ibp_deriv_sin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/FourVertex.lean)
-/
@[path]
lemma ibp_deriv_sin
  {g : ℝ → ℝ}
-- given
  (hdiff : Differentiable ℝ g)
  (hcont_g' : Continuous (deriv g))
  (hcont_g : Continuous g) :
-- imply
  ∫ t in (0:ℝ)..(2*π), deriv g t * sin t = -(∫ t in (0:ℝ)..(2*π), g t * cos t) := by
-- proof
  have ibp := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x _ => hdiff.differentiableAt.hasDerivAt)
    (fun (x : ℝ) _ => hasDerivAt_sin x)
    (hcont_g'.intervalIntegrable 0 (2*π))
    (continuous_cos.intervalIntegrable 0 (2*π))
  simp only [sin_two_pi, sin_zero, mul_zero, sub_zero] at ibp
  have hsplit : ∫ x in (0:ℝ)..(2*π), deriv g x * sin x + g x * cos x =
    (∫ x in (0:ℝ)..(2*π), deriv g x * sin x) + (∫ x in (0:ℝ)..(2*π), g x * cos x) :=
    intervalIntegral.integral_add
      ((hcont_g'.mul continuous_sin).intervalIntegrable 0 (2*π))
      ((hcont_g.mul continuous_cos).intervalIntegrable 0 (2*π))
  linarith [hsplit]
end SturmHurwitz
namespace FourVertex
open Real ClosedCurves


namespace FourVertex

/--
[angle_parametrization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/FourVertex.lean)
-/
@[path]
lemma angle_parametrization
  {c : ℝ → Fin 2 → ℝ}
  {T : ℝ}
-- given
  (hc : IsSimpleClosedCurve c T)
  (hpos : ∀ t, curvature c t > 0) :
-- imply
  ∃ (d : ℝ → Fin 2 → ℝ), IsClosedCurve d (2 * Real.pi) ∧ (∀ t, curvature d t > 0) ∧ (∀ t, (‖deriv d t‖⁻¹) • deriv d t = ![Real.cos t, Real.sin t]) ∧ (∀ t, curvature d t = ‖deriv d t‖⁻¹) := by
-- proof
  have hclosed : IsClosedCurve c T := hc.1
  have hsmooth : ContDiff ℝ ⊤ c := hclosed.smooth
  have hT_pos : T > 0 := hclosed.period_pos
  have hperiodic : ∀ t, c (t + T) = c t := hclosed.periodic
  have hreg : ∀ t, deriv c t ≠ 0 := hclosed.regular
  have hrot := hopf_umlaufsatz c T hc
  have hintegrand_pos : ∀ t, curvature c t * ‖deriv (toEuclidean c) t‖ > 0 := by
    intro t
    have hκ := hpos t
    have hnorm : ‖deriv (toEuclidean c) t‖ > 0 :=
      norm_pos_iff.mpr ((toEuclidean_deriv_eq_zero c hsmooth t).not.mpr (hreg t))
    exact mul_pos hκ hnorm
  have htc_pos : totalCurvature c T > 0 := by
    unfold totalCurvature
    have hcont : ContinuousOn (fun t => curvature c t * ‖deriv (toEuclidean c) t‖)
      (Set.Icc 0 T) :=
      (curvature_integrand_continuous c hsmooth hreg).continuousOn
    exact intervalIntegral.integral_pos hT_pos hcont
      (fun x _ => le_of_lt (hintegrand_pos x))
      ⟨0, Set.left_mem_Icc.mpr (le_of_lt hT_pos), hintegrand_pos 0⟩
  have hrot_one : rotationNumber c T = 1 := by
    cases hrot with
    | inl h => exact h
    | inr h =>
      exfalso
      have : totalCurvature c T = rotationNumber c T * (2 * π) := by
        unfold rotationNumber
        field_simp
      linarith [mul_neg_of_neg_of_pos (show rotationNumber c T < 0 from by linarith)
        (show (2 : ℝ) * π > 0 from by positivity)]
  have htc_eq : totalCurvature c T = 2 * π := by
    have : totalCurvature c T = rotationNumber c T * (2 * π) := by
      unfold rotationNumber; field_simp
    rw [this, hrot_one, one_mul]
  have hut_smooth : ContDiff ℝ ⊤ (unitTangent c) :=
    unitTangent_smooth c hsmooth hreg
  have hut_circle : DegreeTheory.OnUnitCircle (unitTangent c) :=
    unitTangent_onUnitCircle c hsmooth hreg
  obtain ⟨θ, hθ_af⟩ := DegreeTheory.angle_function_exists
    (unitTangent c) hut_smooth hut_circle
  have hθ_smooth : ContDiff ℝ ⊤ θ := hθ_af.1
  have hθ_deriv_pos : ∀ t, 0 < deriv θ t := by
    intro t
    have hθ_hasderiv : HasDerivAt θ (DegreeTheory.angularVelocity (unitTangent c) t) t :=
      angle_function_hasDerivAt_angularVelocity c θ hsmooth hreg hθ_af t
    rw [hθ_hasderiv.deriv]
    exact angularVelocity_unitTangent_pos c t hsmooth hreg (hpos t)
  obtain ⟨_, φ, hφ_left, hφ_right, hφ_smooth, hφ_deriv⟩ :=
    Reparametrization.smooth_increasing_has_smooth_inverse_global θ hθ_smooth hθ_deriv_pos
  have hθ_period : ∀ t, θ (t + T) = θ t + 2 * π :=
    angle_function_period_shift c T θ hclosed hpos hθ_af htc_eq
  set d := c ∘ φ
  have hd_periodic : ∀ t, d (t + 2 * π) = d t := by
    intro t
    show c (φ (t + 2 * π)) = c (φ t)
    have hφ_period : φ (t + 2 * π) = φ t + T :=
      angle_reparam_inverse_period φ θ T hφ_left hφ_right hθ_period (t := t)
    rw [hφ_period]
    exact hperiodic (φ t)
  have hd_smooth : ContDiff ℝ ⊤ d := hsmooth.comp hφ_smooth
  have hd_reg : ∀ t, deriv d t ≠ 0 := by
    intro t
    have hφ_deriv_pos : deriv φ t > 0 :=
      angle_reparam_inverse_deriv_pos θ φ hθ_deriv_pos hφ_left hφ_right hφ_deriv t
    exact comp_deriv_ne_zero c φ hsmooth hφ_smooth (hreg (φ t)) (ne_of_gt hφ_deriv_pos)
  have hd_closed : IsClosedCurve d (2 * π) :=
    ⟨hd_smooth, by positivity, hd_periodic, hd_reg⟩
  have hd_curv_pos : ∀ t, curvature d t > 0 := by
    intro t
    have hφ_pos : ∀ s, 0 < deriv φ s :=
      fun s => angle_reparam_inverse_deriv_pos θ φ hθ_deriv_pos hφ_left hφ_right hφ_deriv s
    have heq := curvature_comp_reparam c φ hsmooth hφ_smooth hφ_pos (fun s => hreg (φ s)) t
    show curvature (c ∘ φ) t > 0
    rw [heq]
    exact hpos (φ t)
  have hd_unit_tangent : ∀ t, (‖deriv d t‖⁻¹) • deriv d t = ![cos t, sin t] := by
    intro t
    exact unit_tangent_angle_reparam c φ θ t hsmooth hφ_smooth hreg
      (fun s => angle_reparam_inverse_deriv_pos θ φ hθ_deriv_pos hφ_left hφ_right hφ_deriv s)
      hθ_af hφ_left
  have hd_curv_eq : ∀ t, curvature d t = ‖deriv d t‖⁻¹ := by
    intro t
    exact curvature_eq_inv_speed_of_angle_param d t hd_smooth (hd_reg t) (hd_unit_tangent t)
  exact ⟨d, hd_closed, hd_curv_pos, hd_unit_tangent, hd_curv_eq⟩

end FourVertex


-- created on 2026-10-23
