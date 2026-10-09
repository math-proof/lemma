import Lemma.Real.MechanicalEnergyOfAngle.eq.Sub.of.Ne_0.Ne_0.Ne_0.DifferentiableAt.Eq
import sympy.physics.vector.kinematics
import sympy.Basic


/--
From \(E=\dfrac{J^2}{2m}A^2-\dfrac{C^2 m}{2J^2}\):
\[
A^2=\left(\dfrac{Cm}{J^2}\right)^2 e^2,\quad e=\sqrt{1+\dfrac{2EJ^2}{mC^2}}.
\]
-/
@[path]
private lemma main
  {r : ℝ → ℝ}
  {A C m J E φ : ℝ}
-- given
  (hm : m ≠ 0)
  (hJ : J ≠ 0)
  (hC : C ≠ 0)
  (hr0 : r φ ≠ 0)
  (hr : DifferentiableAt ℝ r φ)
  (horb : binet_w r = kepler_orbit_reciprocal_signed A C m J)
  (hE : mechanical_energy_of_angle m C J r φ = E) :
-- imply
  A ^ 2 = (C * m / J ^ 2) ^ 2 * (orbit_eccentricity E m C J) ^ 2 := by
-- proof
  have heng :=
    Real.MechanicalEnergyOfAngle.eq.Sub.of.Ne_0.Ne_0.Ne_0.DifferentiableAt.Eq
      hm hJ hr0 hr horb
  have hE' : J ^ 2 / (2 * m) * A ^ 2 - C ^ 2 * m / (2 * J ^ 2) = E := by
    rw [← heng, hE]
  have hJ2 : J ^ 2 ≠ 0 := pow_ne_zero 2 hJ
  have hC2 : C ^ 2 ≠ 0 := pow_ne_zero 2 hC
  have hm2 : (2 * m) ≠ 0 := mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hm
  have hA2 :
      A ^ 2 = (2 * m / J ^ 2) * (E + C ^ 2 * m / (2 * J ^ 2)) := by
    have : J ^ 2 / (2 * m) * A ^ 2 = E + C ^ 2 * m / (2 * J ^ 2) := by
      linarith [hE']
    field_simp [hm, hm2, hJ2] at this ⊢
    linarith
  have hx_nonneg : 0 ≤ 1 + 2 * E * J ^ 2 / (m * C ^ 2) := by
    have hrewrite :
        A ^ 2 = (C * m / J ^ 2) ^ 2 * (1 + 2 * E * J ^ 2 / (m * C ^ 2)) := by
      rw [hA2]
      field_simp [hm, hJ2, hC, hC2]
      ring
    have hcoef : 0 < (C * m / J ^ 2) ^ 2 := by
      have : C * m / J ^ 2 ≠ 0 := by
        refine div_ne_zero ?_ hJ2
        exact mul_ne_zero hC hm
      exact sq_pos_of_ne_zero this
    nlinarith [sq_nonneg A, hrewrite]
  simp only [orbit_eccentricity]
  rw [Real.sq_sqrt hx_nonneg]
  rw [hA2]
  field_simp [hm, hJ2, hC, hC2]
  ring


-- created on 2026-09-29
