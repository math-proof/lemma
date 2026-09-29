import Lemma.Real.DerivDerivBinetW.eq.AddMulS.of.Ne_0.ContDiffAt2
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Combining notes (3)+(4):
\(\ddot r_{\mathrm{angle}}=-\dfrac{J^2}{m^2 r^2}w''\).
-/
@[main]
private lemma main
  {r : ℝ → ℝ}
  {J m φ : ℝ}
-- given
  (hr0 : r φ ≠ 0)
  (hm : m ≠ 0)
  (hr : ContDiffAt ℝ 2 r φ) :
-- imply
  rddot_of_angle r J m φ =
    -(J ^ 2 / (m ^ 2 * (r φ) ^ 2)) * deriv (deriv (binet_w r)) φ := by
-- proof
  have hw := Real.DerivDerivBinetW.eq.AddMulS.of.Ne_0.ContDiffAt2 hr0 hr
  unfold rddot_of_angle
  have hr2 : (r φ) ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  have hr3 : (r φ) ^ 3 ≠ 0 := pow_ne_zero 3 hr0
  have hr4 : (r φ) ^ 4 ≠ 0 := pow_ne_zero 4 hr0
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  rw [hw]
  field_simp [hr0, hr2, hr3, hr4, hm2]
  ring


-- created on 2026-09-29
