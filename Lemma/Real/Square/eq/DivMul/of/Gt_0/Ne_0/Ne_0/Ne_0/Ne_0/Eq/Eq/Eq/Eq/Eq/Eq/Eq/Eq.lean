import Lemma.Real.DivPow.eq.DivMul.of.Ne_0.Ne_0.Ne_0.Ne_0.Eq
import Lemma.Real.EqDivMulMul.of.Ne_0.Ne_0.EqDivMul.EqMulMul
import Lemma.Real.EqDivSub1Square.of.Gt_Neg1.Lt_1.EqMul2AddDivDiv
import Lemma.Real.IntegralArealSpeed.eq.DivMul.of.Ne_0.All_EqAngularMomentum
import Lemma.Real.Mul2.eq.AddDivDiv.of.Ne_0.Ne_0.Gt_Neg1.Lt_1.Eq.Eq.Eq.Eq
import Lemma.Real.OrbitEccentricity.ge.Zero
import Lemma.Real.OrbitEccentricity.lt.One.of.Gt_0.Ne_0.Ne_0.Lt_0
import Lemma.Real.SemiLatusRectum.eq.Div.of.EqNegMulMul
import Lemma.Real.Square.eq.Div.of.Ne_0.Ne_0.Ne_0.Ne_0.EqDivMulMul.EqMulSub1Square.EqDiv
import Lemma.Real.Square.eq.MulSub1Square.of.Ge_0.Lt_1.EqMulSqrtSub1Square
import Lemma.Real.SquareA.eq.MulSquareOrbitEccentricity.of.Ne_0.Ne_0.Ne_0.Ne_0.DifferentiableAt.Eq.Eq
import sympy.physics.vector.kinematics
import sympy.Basic
open Real


/--
Kepler's third law \(T^2=\dfrac{4\pi^2a^3}{GM}\) for a bound gravitational orbit
(\(C=-GMm\), \(E<0\)).  The orbit is `binet_w r = kepler_orbit_reciprocal_signed A C m J`
with \(r\) the radius as a function of the angle, `ρ ∘ θ`-motion has conserved
\(J=m\rho^2\dot\theta\), the major axis is \(2a=r(0)+r(\pi)\), the semi-minor axis is
\(b=a\sqrt{1-e^2}\), and the area swept in one period is the ellipse area \(\pi ab\).
-/
@[main]
private lemma main
  {r ρ θ : ℝ → ℝ}
  {A C G M m J E φ a b T : ℝ}
-- given
  (hm : m > 0)
  (hJ : J ≠ 0)
  (hG : G ≠ 0)
  (hM : M ≠ 0)
  (hC : C = -(G * M * m))
  (hE : E < 0)
  (hr0 : r φ ≠ 0)
  (hr : DifferentiableAt ℝ r φ)
  (horb : binet_w r = kepler_orbit_reciprocal_signed A C m J)
  (hEφ : mechanical_energy_of_angle m C J r φ = E)
  (ha : 2 * a = r 0 + r π)
  (hb : b = a * Real.sqrt (1 - (orbit_eccentricity E m C J) ^ 2))
  (hL : ∀ t, angular_momentum m ρ θ t = J)
  (harea : ∫ t in (0 : ℝ)..T, areal_speed m ρ θ t = π * a * b) :
-- imply
  T ^ 2 = 4 * π ^ 2 * a ^ 3 / (G * M) := by
-- proof
  have hm' : m ≠ 0 := hm.ne'
  have hC' : C ≠ 0 := by
    rw [hC]
    simp [hG, hM, hm']
  have hCm : C * m ≠ 0 := mul_ne_zero hC' hm'
  have he₀ := Real.OrbitEccentricity.ge.Zero E m C J
  have he₁ := Real.OrbitEccentricity.lt.One.of.Gt_0.Ne_0.Ne_0.Lt_0 hm hJ hC' hE
  have hA2 := Real.SquareA.eq.MulSquareOrbitEccentricity.of.Ne_0.Ne_0.Ne_0.Ne_0.DifferentiableAt.Eq.Eq
    hm' hJ hC' hr0 hr horb hEφ
  -- signed eccentricity e' = A J^2 / (C m), e'^2 = e^2
  have hA : A = C * m / J ^ 2 * (A * J ^ 2 / (C * m)) := by
    field_simp [hJ, hCm]
  have he'2 : (A * J ^ 2 / (C * m)) ^ 2 = (orbit_eccentricity E m C J) ^ 2 := by
    have hJ2 : J ^ 2 ≠ 0 := pow_ne_zero 2 hJ
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
  have hb2 := Real.Square.eq.MulSub1Square.of.Ge_0.Lt_1.EqMulSqrtSub1Square he₀ he₁ hb
  have hS := Real.IntegralArealSpeed.eq.DivMul.of.Ne_0.All_EqAngularMomentum (T := T) hm' hL
  have hT := Real.EqDivMulMul.of.Ne_0.Ne_0.EqDivMul.EqMulMul hm' hJ hS harea
  exact Real.Square.eq.Div.of.Ne_0.Ne_0.Ne_0.Ne_0.EqDivMulMul.EqMulSub1Square.EqDiv hm' hJ hG hM hT hb2 hla


-- created on 2026-09-29