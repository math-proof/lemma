import sympy.physics.vector.kinematics
import sympy.Basic


/--
The eccentricity is nonnegative: \(e\ge 0\).
-/
@[main]
private lemma main
  (E m C J : ℝ) :
-- imply
  orbit_eccentricity E m C J ≥ 0 := by
-- proof
  exact Real.sqrt_nonneg _


-- created on 2026-09-29