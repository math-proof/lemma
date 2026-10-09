import Lemma.Real.RddotOfAngle.eq.MulNeg.of.Ne_0.Ne_0.ContDiffAt2
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Binet orbital ODE: from (*) in the angle domain,
\(w''+w=Cm/J^2\).
-/
@[path]
private lemma main
  {r : ℝ → ℝ}
  {J m C φ : ℝ}
-- given
  (hr0 : r φ ≠ 0)
  (hm : m ≠ 0)
  (hJ : J ≠ 0)
  (hr : ContDiffAt ℝ 2 r φ)
  (hstar : rddot_of_angle r J m φ - J ^ 2 / (m ^ 2 * (r φ) ^ 3) =
      -C / (m * (r φ) ^ 2)) :
-- imply
  deriv (deriv (binet_w r)) φ + binet_w r φ = C * m / J ^ 2 := by
-- proof
  have hrd := Real.RddotOfAngle.eq.MulNeg.of.Ne_0.Ne_0.ContDiffAt2 (J := J) hr0 hm hr
  rw [hrd] at hstar
  -- hstar :
  --   -(J²/(m² r²)) w'' - J²/(m² r³) = -C/(m r²)
  have hr2 : (r φ) ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  have hr3 : (r φ) ^ 3 ≠ 0 := pow_ne_zero 3 hr0
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have hJ2 : J ^ 2 ≠ 0 := pow_ne_zero 2 hJ
  -- Multiply both sides by -(m² r² / J²)
  set w'' := deriv (deriv (binet_w r)) φ
  have hmul :
      -(m ^ 2 * (r φ) ^ 2 / J ^ 2) *
          (-(J ^ 2 / (m ^ 2 * (r φ) ^ 2)) * w'' - J ^ 2 / (m ^ 2 * (r φ) ^ 3)) =
        -(m ^ 2 * (r φ) ^ 2 / J ^ 2) * (-C / (m * (r φ) ^ 2)) :=
    congrArg (fun x : ℝ => -(m ^ 2 * (r φ) ^ 2 / J ^ 2) * x) hstar
  have hlhs :
      -(m ^ 2 * (r φ) ^ 2 / J ^ 2) *
          (-(J ^ 2 / (m ^ 2 * (r φ) ^ 2)) * w'' - J ^ 2 / (m ^ 2 * (r φ) ^ 3)) =
        w'' + (r φ)⁻¹ := by
    field_simp [hr0, hr2, hr3, hm2, hJ2]
    try ring
  have hrhs :
      -(m ^ 2 * (r φ) ^ 2 / J ^ 2) * (-C / (m * (r φ) ^ 2)) =
        C * m / J ^ 2 := by
    field_simp [hr0, hr2, hm, hm2, hJ2]
    try ring
  have : w'' + (r φ)⁻¹ = C * m / J ^ 2 := by
    rw [← hlhs, ← hrhs]
    exact hmul
  simpa [binet_w, w''] using this


-- created on 2026-09-29
