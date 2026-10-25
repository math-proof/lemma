import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open MeasureTheory Complex Set Filter Metric
open scoped Topology


namespace Complex.FatouRadialWanted

/-!
# Fatou radial limit theorem for `H∞` on the disc
-/

/-- N1: bounded holomorphic on disc has Lipschitz primitive (Morera + extension). -/
theorem exists_lipschitz_primitive_on_unit_disc
    (f : ℂ → ℂ) {M : ℝ} (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hM : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ M) :
    ∃ G : ℂ → ℂ, ∃ K : NNReal, LipschitzWith K G ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, HasDerivAt G (f z)
        z := by
  obtain ⟨F, hF⟩ := hf.isExactOn_ball
  have hconv : Convex ℝ (Metric.ball (0 : ℂ) 1) := convex_ball _ _
  have hderiv : ∀ x ∈ Metric.ball (0 : ℂ) 1,
      HasDerivWithinAt F (f x) (Metric.ball (0 : ℂ) 1) x :=
    fun x hx => (hF x hx).hasDerivWithinAt
  have hbound : ∀ x ∈ Metric.ball (0 : ℂ) 1, ‖f x‖₊ ≤ Real.toNNReal M := by
    intro x hx
    exact NNReal.le_toNNReal_of_coe_le (hM x hx)
  have hlip : LipschitzOnWith (Real.toNNReal M) F (Metric.ball (0 : ℂ) 1) :=
    hconv.lipschitzOnWith_of_nnnorm_hasDerivWithin_le hderiv hbound
  obtain ⟨G, hGlip, hGeq⟩ := hlip.extend_finite_dimension
  refine ⟨G, _, hGlip, ?_⟩
  intro z hz
  have hmem : Metric.ball (0 : ℂ) 1 ∈ 𝓝 z := isOpen_ball.mem_nhds hz
  have hev : G =ᶠ[𝓝 z] F := Filter.eventuallyEq_of_mem hmem (fun w hw => (hGeq hw).symm)
  exact (hF z hz).congr_of_eventuallyEq hev

/-- N2: boundary trace of Lipschitz map is a.e. differentiable (1-D Rademacher). -/
theorem ae_differentiableAt_circle_comp {K : NNReal} {G : ℂ → ℂ} (hG : LipschitzWith K G) :
    ∀ᵐ θ : ℝ, DifferentiableAt ℝ (fun t : ℝ => G (Complex.exp ((t : ℂ) * Complex.I))) θ := by
  have he : (fun t : ℝ => G (Complex.exp ((t : ℂ) * Complex.I))) = G ∘ (circleMap 0 1) := by
    funext t
    simp [circleMap_zero]
  rw [he]
  exact (hG.comp (lipschitzWith_circleMap 0 1)).ae_differentiableAt_real

/-- N8: Lorentzian mass bound on [-π, π]. -/
theorem integral_lorentzian_le_pi {a : ℝ} (ha : 0 < a) :
    ∫ t in (-Real.pi)..Real.pi, a / (a ^ 2 + t ^ 2) ≤ Real.pi := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hderiv : ∀ x : ℝ, HasDerivAt (fun t => Real.arctan (t / a)) (a / (a ^ 2 + x ^ 2)) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => t / a) (1 / a) x :=
      (hasDerivAt_id x).div_const a
    have h2 := (Real.hasDerivAt_arctan (x / a)).comp x h1
    have heq : (1 / (1 + (x / a) ^ 2)) * (1 / a) = a / (a ^ 2 + x ^ 2) := by
      field_simp
    rwa [heq] at h2
  have hcont : Continuous (fun t : ℝ => a / (a ^ 2 + t ^ 2)) := by
    apply Continuous.div continuous_const
    · fun_prop
    · intro t; positivity
  have hint : IntervalIntegrable (fun t : ℝ => a / (a ^ 2 + t ^ 2)) volume (-Real.pi) Real.pi :=
    hcont.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x) hint
  rw [hFTC]
  have h1 := Real.arctan_lt_pi_div_two (Real.pi / a)
  have h2 := Real.neg_pi_div_two_lt_arctan ((-Real.pi) / a)
  linarith [Real.pi_pos]

/-- N7a: quadratic lower bound for Poisson denominator. -/
theorem fatou_kernel_denom_bound {r t : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1)
    (ht : |t| ≤ Real.pi) :
    1 - 2 * r * Real.cos t + r ^ 2 ≥ (2 / Real.pi ^ 2) * ((1 - r) ^ 2 + t ^ 2) := by
  have hcos : Real.cos t ≤ 1 - 2 / Real.pi ^ 2 * t ^ 2 :=
    Real.cos_le_one_sub_mul_cos_sq ht
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hr_nn : 0 ≤ r := by linarith
  have h2 : (1 - r) ^ 2 + 2 * r * (1 - Real.cos t) = 1 - 2 * r * Real.cos t + r ^ 2 := by ring
  rw [← h2]
  have h1 : 2 * r * (1 - Real.cos t) ≥ 2 * r * (2 / Real.pi ^ 2 * t ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hr2' : 2 * r * (2 / Real.pi ^ 2 * t ^ 2) ≥ (2 / Real.pi ^ 2) * t ^ 2 := by
    have : 2 * r * (2 / Real.pi ^ 2 * t ^ 2) = (2 * r) * ((2 / Real.pi ^ 2) * t ^ 2) := by ring
    rw [this]
    have hr : (1 : ℝ) ≤ 2 * r := by linarith
    have hnn : 0 ≤ (2 / Real.pi ^ 2) * t ^ 2 := by positivity
    calc (2 / Real.pi ^ 2) * t ^ 2 = 1 * ((2 / Real.pi ^ 2) * t ^ 2) := by ring
      _ ≤ (2 * r) * ((2 / Real.pi ^ 2) * t ^ 2) := by
          apply mul_le_mul_of_nonneg_right hr hnn
  have hle : (2 / Real.pi ^ 2) * ((1 - r) ^ 2 + t ^ 2)
      ≤ (1 - r) ^ 2 + (2 / Real.pi ^ 2) * t ^ 2 := by
    have hfrac : 2 / Real.pi ^ 2 ≤ 1 := by
      rw [div_le_one hpi2]
      nlinarith [hpi, Real.pi_pos]
    nlinarith [sq_nonneg ((1 - r)), sq_nonneg t, hfrac]
  linarith

theorem poly_ident {u r : ℂ} (hu : u ≠ 0) :
    u * (u⁻¹ - r) ^ 2 - u⁻¹ * (u - r) ^ 2 = (r ^ 2 - 1) * (u - u⁻¹) := by
  field_simp
  ring

theorem rat_ident {u r : ℂ} (hr : r ≠ 0) (h1 : u - r ≠ 0) (h2 : u - r⁻¹ ≠ 0) (hu : u ≠ 0) :
    u * (((u - r) ^ 2)⁻¹ - (r ^ 2)⁻¹ * ((u - r⁻¹) ^ 2)⁻¹)
      = (r ^ 2 - 1) * (u - u⁻¹) / ((u - r) * (u⁻¹ - r)) ^ 2 := by
  have h3 : u⁻¹ - r ≠ 0 := by
    intro h
    apply h2
    have hr2 : u⁻¹ = r := sub_eq_zero.mp h
    have hu2 : u = r⁻¹ := by rw [← hr2, inv_inv]
    rw [hu2, sub_self]
  have hD : (u - r) * (u⁻¹ - r) ≠ 0 := mul_ne_zero h1 h3
  have hD2 : ((u - r) * (u⁻¹ - r)) ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hA2 : ((u - r) ^ 2) ≠ 0 := pow_ne_zero 2 h1
  have hB2 : ((u⁻¹ - r) ^ 2) ≠ 0 := pow_ne_zero 2 h3
  have hr2 : (r : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have erel : (u - r⁻¹) = -(u / r) * (u⁻¹ - r) := by
    field_simp
    ring
  have step1 : (-(u / r) * (u⁻¹ - r)) ^ 2 = (u ^ 2 / r ^ 2) * (u⁻¹ - r) ^ 2 := by ring
  have step2 : ((u ^ 2 / r ^ 2) * (u⁻¹ - r) ^ 2)⁻¹
      = (r ^ 2 / u ^ 2) * (((u⁻¹ - r) ^ 2)⁻¹) := by
    rw [mul_inv, inv_div]
  have step3 : (r ^ 2)⁻¹ * (r ^ 2 / u ^ 2) = ((u ^ 2)⁻¹ : ℂ) := by
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hr2, one_mul]
  have inner : (r ^ 2)⁻¹ * (r ^ 2 / u ^ 2 * (((u⁻¹ - r) ^ 2)⁻¹ : ℂ))
      = (u ^ 2)⁻¹ * (((u⁻¹ - r) ^ 2)⁻¹ : ℂ) := by
    rw [← mul_assoc, step3]
  have cu : (u : ℂ) * ((u ^ 2)⁻¹) = u⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  rw [eq_div_iff hD2, erel, step1, step2, inner, mul_pow]
  have expand : (u : ℂ) * (((u - r) ^ 2)⁻¹ - (u ^ 2)⁻¹ * (((u⁻¹ - r) ^ 2)⁻¹))
      * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
      = u * ((u⁻¹ - r) ^ 2) - u⁻¹ * ((u - r) ^ 2) := by
    have eA : (u : ℂ) * (((u - r) ^ 2)⁻¹) * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
        = u * ((u⁻¹ - r) ^ 2) := by
      rw [show u * ((u - r) ^ 2)⁻¹ * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
        = u * (((u - r) ^ 2)⁻¹ * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)) by ring,
        show ((u - r) ^ 2)⁻¹ * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
          = ((u - r) ^ 2)⁻¹ * ((u - r) ^ 2) * ((u⁻¹ - r) ^ 2) by ring,
        inv_mul_cancel₀ hA2, one_mul]
    have eB : (u : ℂ) * ((u ^ 2)⁻¹ * (((u⁻¹ - r) ^ 2)⁻¹))
        * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
        = u⁻¹ * ((u - r) ^ 2) := by
      rw [show u * ((u ^ 2)⁻¹ * ((u⁻¹ - r) ^ 2)⁻¹) * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
        = (u * (u ^ 2)⁻¹) * ((((u⁻¹ - r) ^ 2)⁻¹) * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)) by ring,
        cu,
        show ((u⁻¹ - r) ^ 2)⁻¹ * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
          = ((u⁻¹ - r) ^ 2)⁻¹ * ((u⁻¹ - r) ^ 2) * ((u - r) ^ 2) by ring,
        inv_mul_cancel₀ hB2, one_mul]
    linear_combination eA - eB
  rw [expand]
  exact poly_ident hu

theorem exp_sub_inv {t : ℝ} :
    Complex.exp ((t : ℂ) * Complex.I) - (Complex.exp ((t : ℂ) * Complex.I))⁻¹
      = 2 * Complex.I * Complex.sin ((t : ℂ)) := by
  have h := Complex.two_sin ((t : ℂ))
  simp only [neg_mul] at h
  have hinv : (Complex.exp ((t : ℂ) * Complex.I))⁻¹
      = Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [← Complex.exp_neg]
  rw [hinv]
  have hI : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
  linear_combination (Complex.exp (↑t * Complex.I) - Complex.exp (-(↑t * Complex.I))) * hI
    - h * Complex.I

theorem exp_prod_eq {t : ℝ} {r : ℝ} :
    (Complex.exp ((t : ℂ) * Complex.I) - (r : ℂ))
      * ((Complex.exp ((t : ℂ) * Complex.I))⁻¹ - (r : ℂ))
      = ((1 - 2 * r * Real.cos t + r ^ 2 : ℝ) : ℂ) := by
  have h := Complex.two_cos ((t : ℂ))
  simp only [neg_mul] at h
  have hinv : (Complex.exp ((t : ℂ) * Complex.I))⁻¹
      = Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [← Complex.exp_neg]
  have huu : Complex.exp ((t : ℂ) * Complex.I) * (Complex.exp ((t : ℂ) * Complex.I))⁻¹ = 1 :=
    mul_inv_cancel₀ (Complex.exp_ne_zero _)
  have hsum : Complex.exp ((t : ℂ) * Complex.I) + (Complex.exp ((t : ℂ) * Complex.I))⁻¹
      = 2 * Complex.cos ((t : ℂ)) := by
    rw [hinv]; linear_combination -h
  have hexpand : (Complex.exp ((t : ℂ) * Complex.I) - (r : ℂ))
      * ((Complex.exp ((t : ℂ) * Complex.I))⁻¹ - (r : ℂ))
      = 1 - (r : ℂ) * (Complex.exp ((t : ℂ) * Complex.I)
        + (Complex.exp ((t : ℂ) * Complex.I))⁻¹) + (r : ℂ) ^ 2 := by
    linear_combination huu
  rw [hexpand, hsum]
  push_cast [Complex.ofReal_cos]
  ring

theorem fatou_kernel_identity {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (Complex.exp ((t : ℂ) * Complex.I)) *
      ((Complex.exp ((t : ℂ) * Complex.I) - (r : ℂ)) ^ (-2 : ℤ)
        - ((r : ℂ) ^ 2)⁻¹ * (Complex.exp ((t : ℂ) * Complex.I) - (r : ℂ)⁻¹) ^ (-2 : ℤ))
      = -2 * Complex.I * (((1 - r ^ 2) * Real.sin t / (1 - 2 * r * Real.cos t + r ^ 2) ^ 2 : ℝ) :
          ℂ) := by
  have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr0
  have hu : Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hnorm : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have hur : Complex.exp ((t : ℂ) * Complex.I) - (r : ℂ) ≠ 0 := by
    intro h
    have heq : Complex.exp ((t : ℂ) * Complex.I) = (r : ℂ) := sub_eq_zero.mp h
    have h1 : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = ‖(r : ℂ)‖ := by rw [heq]
    rw [hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] at h1
    linarith
  have hurinv : Complex.exp ((t : ℂ) * Complex.I) - (r : ℂ)⁻¹ ≠ 0 := by
    intro h
    have heq : Complex.exp ((t : ℂ) * Complex.I) = (r : ℂ)⁻¹ := sub_eq_zero.mp h
    have h1 : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = ‖(r : ℂ)⁻¹‖ := by rw [heq]
    rw [hnorm, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] at h1
    have hrinv : (1 : ℝ) < r⁻¹ := (one_lt_inv₀ hr0).mpr hr1
    linarith
  rw [zpow_neg, zpow_ofNat, zpow_neg, zpow_ofNat]
  have hrat := rat_ident hr0' hur hurinv hu
  rw [hrat, exp_sub_inv, exp_prod_eq, ← Complex.ofReal_sin]
  push_cast
  ring

theorem circleIntegral_sub_sq_eq_deriv_unit_disc
    {G g : ℂ → ℂ} (hGcont : Continuous G)
    (hG : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasDerivAt G (g z) z)
    {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    (∮ z in C((0 : ℂ), 1), (z - w) ^ (-2 : ℤ) • G z)
      = (2 * (Real.pi : ℂ) * Complex.I) * g w := by
  have hdiff : DifferentiableOn ℂ G (Metric.ball (0 : ℂ) 1) :=
    fun z hz => ((hG z hz).hasDerivWithinAt).differentiableWithinAt
  have hcont : ContinuousOn G (closure (Metric.ball (0 : ℂ) 1)) := by
    rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
    exact hGcont.continuousOn
  have hDiff : DiffContOnCl ℂ G (Metric.ball (0 : ℂ) 1) := DiffContOnCl.mk hdiff hcont
  -- Cauchy formula: Φ = (2πi) • G on D
  have hCauchy : ∀ w' ∈ Metric.ball (0 : ℂ) 1,
      (∮ z in C((0 : ℂ), 1), (z - w')⁻¹ • G z) = (2 * (Real.pi : ℂ) * Complex.I) • G w' :=
    fun w' hw' => hDiff.circleIntegral_sub_inv_smul hw'
  have hmem : Metric.ball (0 : ℂ) 1 ∈ 𝓝 w := isOpen_ball.mem_nhds hw
  have hPhi : (fun w' => ∮ z in C((0 : ℂ), 1), (z - w')⁻¹ • G z)
      =ᶠ[𝓝 w] ((2 * (Real.pi : ℂ) * Complex.I) • G) :=
    Filter.eventuallyEq_of_mem hmem (fun w' hw' => hCauchy w' hw')
  have hderiv1 : HasDerivAt ((2 * (Real.pi : ℂ) * Complex.I) • G)
      ((2 * (Real.pi : ℂ) * Complex.I) • g w) w :=
    HasDerivAt.const_smul _ (hG w hw)
  have hderiv1' : HasDerivAt (fun w' => ∮ z in C((0 : ℂ), 1), (z - w')⁻¹ • G z)
      ((2 * (Real.pi : ℂ) * Complex.I) • g w) w :=
    hderiv1.congr_of_eventuallyEq hPhi
  have hCirc : CircleIntegrable G (0 : ℂ) 1 :=
    hGcont.continuousOn.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hwsph : w ∉ sphere (0 : ℂ) |1| := by
    rw [abs_one]
    intro hcon
    have h1 : dist w 0 = 1 := Metric.mem_sphere.mp hcon
    have h2 : dist w 0 < 1 := Metric.mem_ball.mp hw
    rw [dist_zero_right] at h1 h2
    linarith
  have hderiv2 : HasDerivAt (fun w' => ∮ z in C((0 : ℂ), 1), (z - w')⁻¹ • G z)
      (∮ z in C((0 : ℂ), 1), (z - w) ^ (-2 : ℤ) • G z) w :=
    hasDerivAt_circleIntegral_sub_inv_smul hCirc hwsph
  have heq := hderiv1'.unique hderiv2
  rw [smul_eq_mul] at heq
  exact heq.symm

theorem circleIntegral_reflected_pole_eq_zero
    {G : ℂ → ℂ} (hGcont : Continuous G)
    (hGdiff : ∀ z ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℂ G z)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∮ z in C((0 : ℂ), 1), (z - (r : ℂ)⁻¹) ^ (-2 : ℤ) • G z) = 0 := by
  have hrinv_gt : (1 : ℝ) < r⁻¹ := (one_lt_inv₀ hr0).mpr hr1
  have hcnorm : ‖(r : ℂ)⁻¹‖ = r⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hne : ∀ z : ℂ, ‖z‖ ≤ 1 → z - (r : ℂ)⁻¹ ≠ 0 := by
    intro z hz hcon
    have heq : z = (r : ℂ)⁻¹ := sub_eq_zero.mp hcon
    rw [heq, hcnorm] at hz
    linarith
  have hsmul : (fun z : ℂ => (z - (r : ℂ)⁻¹) ^ (-2 : ℤ) • G z)
      = (fun z : ℂ => (z - (r : ℂ)⁻¹) ^ (-2 : ℤ) * G z) := by
    funext z; exact smul_eq_mul _ _
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable
    (by norm_num : (0 : ℝ) ≤ 1) (s := ∅) countable_empty ?_ ?_
  · rw [hsmul]
    apply ContinuousOn.mul _ hGcont.continuousOn
    apply ContinuousOn.zpow₀ (ContinuousOn.sub continuousOn_id continuousOn_const) (-2)
    intro a ha
    left
    apply hne
    have hdist : dist a 0 ≤ 1 := Metric.mem_closedBall.mp ha
    rwa [dist_zero_right] at hdist
  · intro z hz
    have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
      simpa using hz.1
    have hzne : z - (r : ℂ)⁻¹ ≠ 0 := by
      apply hne
      have hdist : dist z 0 < 1 := Metric.mem_ball.mp hzmem
      rw [dist_zero_right] at hdist
      linarith
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (w - (r : ℂ)⁻¹) ^ (-2 : ℤ)) z :=
      (differentiableAt_id.sub_const _).zpow (Or.inl hzne)
    rw [hsmul]
    exact hpow.mul (hGdiff z hzmem)

end Complex.FatouRadialWanted
