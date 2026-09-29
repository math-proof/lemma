import sympy.physics.vector.kinematics
import sympy.Basic


/--
Eccentricity definition:
\(e=\sqrt{1+\dfrac{2EJ^2}{mC^2}}\).
-/
@[main]
private lemma main
  (E m C J : ℝ) :
-- imply
  orbit_eccentricity E m C J = Real.sqrt (1 + 2 * E * J ^ 2 / (m * C ^ 2)) := by
-- proof
  rfl


-- created on 2026-09-29
