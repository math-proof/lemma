import Lemma.Real.ArealSpeed.eq.Div.of.Ne_0.EqAngularMomentum
import Lemma.Real.Deriv.eq.Div_Mul_Square.of.Ne_0.Ne_0.EqAngularMomentum
import Lemma.Real.DivPow.eq.DivMul.of.Ne_0.Ne_0.Ne_0.Ne_0.Eq
import Lemma.Real.EqDivMulMul.of.Ne_0.Ne_0.EqDivMul.EqMulMul
import Lemma.Real.EqDivSub1Square.of.Gt_Neg1.Lt_1.EqMul2AddDivDiv
import Lemma.Real.Gt_0Sub1MulCos.of.Gt_Neg1.Lt_1
import Lemma.Real.IntegralArealSpeed.eq.MulMul.of.Ne_0.Gt_Neg1.Lt_1.All_DifferentiableAt.ContinuousOn.Eq.All_Eq
import Lemma.Real.InvKeplerOrbitReciprocalSigned.eq.Div.of.Ne_0.Ne_0.Ne_0.Eq.Eq
import Lemma.Real.MechanicalEnergyOfAngle.eq.Sub.of.Ne_0.Ne_0.Ne_0.DifferentiableAt.Eq
import Lemma.Real.Mul2.eq.AddDivDiv.of.Ne_0.Ne_0.Gt_Neg1.Lt_1.Eq.Eq.Eq.Eq
import Lemma.Real.OrbitEccentricity.ge.Zero
import Lemma.Real.OrbitEccentricity.lt.One.of.Gt_0.Ne_0.Ne_0.Lt_0
import Lemma.Real.SemiLatusRectum.eq.Div.of.EqNegMulMul
import Lemma.Real.Square.eq.Div.of.Ne_0.Ne_0.Ne_0.Ne_0.EqDivMulMul.EqMulSub1Square.EqDiv
import Lemma.Real.SquareA.eq.MulSquareOrbitEccentricity.of.Ne_0.Ne_0.Ne_0.Ne_0.DifferentiableAt.Eq.Eq
import sympy.physics.vector.kinematics
import sympy.Basic
open Real


/--
Kepler's third law \(T^2=\dfrac{4\pi^2a^3}{GM}\) for a bound gravitational orbit
(\(C=-GMm\), \(E<0\)), from the orbit equation alone.
The orbit is `binet_w r = kepler_orbit_reciprocal_signed A C m J` (radius as a function of the
angle), the motion is `ρ = r ∘ θ` on \([0,T]\) with conserved \(J=m\rho^2\dot\theta\),
the major axis is \(2a=r(0)+r(\pi)\), and one period \(T\) is the time in which the polar angle
advances by \(2\pi\).
Nonvanishing / differentiability of \(r\), \(G\ne0\), \(M\ne0\), and the regularity of
\(\theta\) are all derived rather than assumed.
-/
@[path]
private lemma main
  {r ρ θ : ℝ → ℝ}
  {A C G M m J E φ a T : ℝ}
-- given
  (hm : m > 0)
  (hJ : J ≠ 0)
  (hE : E < 0)
  (hC : C = -(G * M * m))
  (horb : binet_w r = kepler_orbit_reciprocal_signed A C m J)
  (hEφ : mechanical_energy_of_angle m C J r φ = E)
  (ha : 2 * a = r 0 + r π)
  (hL : ∀ t ∈ Set.uIcc 0 T, angular_momentum m ρ θ t = J)
  (hρ : ∀ t ∈ Set.uIcc 0 T, ρ t = r (θ t))
  (hθT : θ T = θ 0 + 2 * π) :
-- imply
  T ^ 2 = 4 * π ^ 2 * a ^ 3 / (G * M) := by
-- proof
  have hm' : m ≠ 0 := hm.ne'
  have hJ2 : J ^ 2 ≠ 0 := pow_ne_zero 2 hJ
  have hrk : ∀ x, r x = (kepler_orbit_reciprocal_signed A C m J x)⁻¹ := by
    intro x
    rw [← congrFun horb x, binet_w, inv_inv]
  -- r φ ≠ 0: otherwise the energy would be 0
  have hr0 : r φ ≠ 0 := by
    intro h0
    have h : mechanical_energy_of_angle m C J r φ = 0 := by
      simp [mechanical_energy_of_angle, h0]
    linarith
  have hkφ : kepler_orbit_reciprocal_signed A C m J φ ≠ 0 := by
    intro h
    apply hr0
    rw [hrk φ, h, inv_zero]
  have hr : DifferentiableAt ℝ r φ := by
    have hd : DifferentiableAt ℝ (kepler_orbit_reciprocal_signed A C m J) φ := by
      have h : DifferentiableAt ℝ (fun x => A * Real.cos x + -C * m / J ^ 2) φ := by fun_prop
      exact h
    have : r = fun x => (kepler_orbit_reciprocal_signed A C m J x)⁻¹ := funext hrk
    rw [this]
    exact hd.inv hkφ
  -- C ≠ 0: otherwise E ≥ 0
  have hC' : C ≠ 0 := by
    intro h0
    have heng := Real.MechanicalEnergyOfAngle.eq.Sub.of.Ne_0.Ne_0.Ne_0.DifferentiableAt.Eq
      hm' hJ hr0 hr horb
    rw [hEφ, h0] at heng
    have : 0 ≤ J ^ 2 / (2 * m) * A ^ 2 := by positivity
    have h : E = J ^ 2 / (2 * m) * A ^ 2 := by
      rw [heng]
      simp
    linarith
  have hG : G ≠ 0 := by
    intro h
    apply hC'
    rw [hC, h]
    simp
  have hM : M ≠ 0 := by
    intro h
    apply hC'
    rw [hC, h]
    simp
  have hCm : C * m ≠ 0 := mul_ne_zero hC' hm'
  have he₀ := Real.OrbitEccentricity.ge.Zero E m C J
  have he₁ := Real.OrbitEccentricity.lt.One.of.Gt_0.Ne_0.Ne_0.Lt_0 hm hJ hC' hE
  have hA2 := Real.SquareA.eq.MulSquareOrbitEccentricity.of.Ne_0.Ne_0.Ne_0.Ne_0.DifferentiableAt.Eq.Eq
    hm' hJ hC' hr0 hr horb hEφ
  have hA : A = C * m / J ^ 2 * (A * J ^ 2 / (C * m)) := by
    field_simp [hJ, hCm]
  have he'2 : (A * J ^ 2 / (C * m)) ^ 2 = (orbit_eccentricity E m C J) ^ 2 := by
    have : (A * J ^ 2 / (C * m)) ^ 2 = A ^ 2 * (J ^ 2 / (C * m)) ^ 2 := by ring
    rw [this, hA2]
    field_simp [hJ2, hCm]
  have he'₁ : A * J ^ 2 / (C * m) < 1 := by nlinarith
  have he'₀ : -1 < A * J ^ 2 / (C * m) := by nlinarith
  have hp := Real.SemiLatusRectum.eq.Div.of.EqNegMulMul (J := J) hC
  have h2a := Real.Mul2.eq.AddDivDiv.of.Ne_0.Ne_0.Gt_Neg1.Lt_1.Eq.Eq.Eq.Eq hJ hCm he'₀ he'₁ hA rfl horb ha
  have haa := Real.EqDivSub1Square.of.Gt_Neg1.Lt_1.EqMul2AddDivDiv he'₀ he'₁ h2a
  have hden : 1 - (A * J ^ 2 / (C * m)) ^ 2 ≠ 0 := by nlinarith
  have hla : a * (1 - (orbit_eccentricity E m C J) ^ 2) = J ^ 2 / (G * M * m ^ 2) := by
    rw [← he'2, haa, ← hp]
    exact div_mul_cancel₀ _ hden
  -- the polar form r x = p / (1 - e cos x) with signed eccentricity e
  have hr' : ∀ x, r x = semi_latus_rectum C m J / (1 - A * J ^ 2 / (C * m) * Real.cos x) := by
    intro x
    rw [hrk x]
    exact Real.InvKeplerOrbitReciprocalSigned.eq.Div.of.Ne_0.Ne_0.Ne_0.Eq.Eq hJ hCm
      (Real.Gt_0Sub1MulCos.of.Gt_Neg1.Lt_1 he'₀ he'₁ x).ne' hA rfl
  have hp0 : semi_latus_rectum C m J ≠ 0 := by
    rw [hp]
    exact div_ne_zero hJ2 (by simp [hG, hM, hm'])
  have hrne : ∀ x, r x ≠ 0 := fun x => by
    rw [hr' x]
    exact div_ne_zero hp0 (Real.Gt_0Sub1MulCos.of.Gt_Neg1.Lt_1 he'₀ he'₁ x).ne'
  have hrc : Continuous r := by
    have : r = fun x => semi_latus_rectum C m J / (1 - A * J ^ 2 / (C * m) * Real.cos x) :=
      funext hr'
    rw [this]
    refine Continuous.div continuous_const (by fun_prop) fun x => ?_
    exact (Real.Gt_0Sub1MulCos.of.Gt_Neg1.Lt_1 he'₀ he'₁ x).ne'
  -- regularity of θ on [0, T]
  have hθ : ∀ t ∈ Set.uIcc 0 T, DifferentiableAt ℝ θ t := by
    intro t ht
    by_contra hnd
    have h0 : deriv θ t = 0 := deriv_zero_of_not_differentiableAt hnd
    have h := hL t ht
    simp only [angular_momentum, specific_angular_momentum, h0, mul_zero] at h
    exact hJ h.symm
  have hθc : ContinuousOn θ (Set.uIcc 0 T) := fun t ht =>
    (hθ t ht).continuousAt.continuousWithinAt
  have hθ' : ContinuousOn (deriv θ) (Set.uIcc 0 T) := by
    have hcont : ContinuousOn (fun t => J / (m * (r (θ t)) ^ 2)) (Set.uIcc 0 T) := by
      refine ContinuousOn.div continuousOn_const ?_ fun t _ => ?_
      · exact continuousOn_const.mul ((hrc.comp_continuousOn hθc).pow 2)
      · exact mul_ne_zero hm' (pow_ne_zero 2 (hrne _))
    refine hcont.congr fun t ht => ?_
    have := Real.Deriv.eq.Div_Mul_Square.of.Ne_0.Ne_0.EqAngularMomentum (ρ := ρ) (θ := θ) hm'
      (by rw [hρ t ht]; exact hrne _) (hL t ht)
    rw [this, hρ t ht]
  -- swept area over one period is the ellipse area
  have harea := Real.IntegralArealSpeed.eq.MulMul.of.Ne_0.Gt_Neg1.Lt_1.All_DifferentiableAt.ContinuousOn.Eq.All_Eq
    (ρ := fun t => r (θ t)) hm' he'₀ he'₁ hθ hθ' hθT hr' fun t => rfl
  rw [← haa, he'2] at harea
  have harea' : ∫ t in (0 : ℝ)..T, areal_speed m ρ θ t =
      π * a * (a * Real.sqrt (1 - (orbit_eccentricity E m C J) ^ 2)) := by
    rw [← harea]
    refine intervalIntegral.integral_congr fun t ht => ?_
    simp only [areal_speed, angular_momentum, specific_angular_momentum, hρ t ht]
  have hb2 : (a * Real.sqrt (1 - (orbit_eccentricity E m C J) ^ 2)) ^ 2 =
      a ^ 2 * (1 - (orbit_eccentricity E m C J) ^ 2) := by
    have h : 0 ≤ 1 - (orbit_eccentricity E m C J) ^ 2 := by nlinarith
    rw [mul_pow, Real.sq_sqrt h]
  have hS : ∫ t in (0 : ℝ)..T, areal_speed m ρ θ t = J * T / (2 * m) := by
    rw [intervalIntegral.integral_congr (g := fun _ => J / (2 * m)) fun t ht =>
      Real.ArealSpeed.eq.Div.of.Ne_0.EqAngularMomentum hm' (hL t ht)]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
  have hT := Real.EqDivMulMul.of.Ne_0.Ne_0.EqDivMul.EqMulMul hm' hJ hS harea'
  exact Real.Square.eq.Div.of.Ne_0.Ne_0.Ne_0.Ne_0.EqDivMulMul.EqMulSub1Square.EqDiv hm' hJ hG hM hT hb2 hla


-- created on 2026-09-29