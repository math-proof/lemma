import sympy.physics.vector.kinematics
import sympy.Basic


/--
For the gravitational constant \(C=-GMm\), the semi-latus rectum is
\(p=-J^2/(Cm)=\dfrac{J^2}{GMm^2}\).
-/
@[main]
private lemma main
  {C G M m J : ℝ}
-- given
  (hC : C = -(G * M * m)) :
-- imply
  semi_latus_rectum C m J = J ^ 2 / (G * M * m ^ 2) := by
-- proof
  subst hC
  simp only [semi_latus_rectum]
  rw [neg_mul, neg_div_neg_eq]
  ring


-- created on 2026-09-29