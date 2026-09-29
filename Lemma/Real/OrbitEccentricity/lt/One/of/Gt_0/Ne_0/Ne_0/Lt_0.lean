import sympy.physics.vector.kinematics
import sympy.Basic


/--
A bound orbit (\(E<0\)) is elliptical: \(e=\sqrt{1+\dfrac{2EJ^2}{mC^2}}<1\).
-/
@[main]
private lemma main
  {E m C J : ℝ}
-- given
  (hm : m > 0)
  (hJ : J ≠ 0)
  (hC : C ≠ 0)
  (hE : E < 0) :
-- imply
  orbit_eccentricity E m C J < 1 := by
-- proof
  have hJ2 : J ^ 2 > 0 := by positivity
  have hC2 : C ^ 2 > 0 := by positivity
  have h : 2 * E * J ^ 2 / (m * C ^ 2) < 0 := by
    apply div_neg_of_neg_of_pos
    · nlinarith
    · positivity
  simp only [orbit_eccentricity]
  rw [Real.sqrt_lt' (by norm_num)]
  linarith


-- created on 2026-09-29