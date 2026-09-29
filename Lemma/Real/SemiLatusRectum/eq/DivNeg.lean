import sympy.physics.vector.kinematics
import sympy.Basic


/--
Semi-latus rectum: \(p=-J^2/(Cm)\).
-/
@[main]
private lemma main
  (C m J : ℝ) :
-- imply
  semi_latus_rectum C m J = -(J ^ 2) / (C * m) := by
-- proof
  rfl


-- created on 2026-09-29
