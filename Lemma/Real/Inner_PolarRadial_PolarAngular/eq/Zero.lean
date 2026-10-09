import sympy.physics.vector.kinematics
import sympy.Basic


/--
Polar unit vectors are orthogonal: \(\hat{r}\perp\hat{\theta}\).
-/
@[path]
private lemma main
  (θ : ℝ) :
-- imply
  inner ℝ (polar_radial θ) (polar_angular θ) = 0 := by
-- proof
  simp [polar_radial, polar_angular, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring


-- created on 2026-09-28
