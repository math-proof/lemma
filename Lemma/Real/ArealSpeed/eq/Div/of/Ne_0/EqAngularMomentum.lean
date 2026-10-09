import sympy.physics.vector.kinematics
import sympy.Basic


/--
Kepler's second law: areal speed equals \(J/(2m)\) when \(J=m\rho^2\dot\theta\).
-/
@[path]
private lemma main
  {m J : ℝ}
  {ρ θ : ℝ → ℝ}
  {t : ℝ}
-- given
  (_hm : m ≠ 0)
  (hJ : angular_momentum m ρ θ t = J) :
-- imply
  areal_speed m ρ θ t = J / (2 * m) := by
-- proof
  simp only [areal_speed, hJ]


-- created on 2026-09-29
