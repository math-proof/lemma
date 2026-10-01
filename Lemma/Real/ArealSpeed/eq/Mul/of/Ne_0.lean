import sympy.physics.vector.kinematics
import sympy.Basic


/--
Polar expression of areal speed:
\(\dfrac{ds}{dt}=\dfrac12\rho^2\dot\theta=\dfrac{J}{2m}\).
-/
@[main]
private lemma main
  {m : ℝ}
  {ρ θ : ℝ → ℝ}
  {t : ℝ}
-- given
  (hm : m ≠ 0) :
-- imply
  areal_speed m ρ θ t = (1 / 2) * (ρ t) ^ 2 * deriv θ t := by
-- proof
  simp only [areal_speed, angular_momentum, specific_angular_momentum]
  field_simp [hm]
  try ring


-- created on 2026-09-29
