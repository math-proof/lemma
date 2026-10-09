import Lemma.Real.Norm.eq.Sqrt
import sympy.physics.vector.kinematics
import sympy.Basic


/-- Polar angular unit vector has length one: \(|\hat{\theta}|=1\). -/
@[path]
private lemma main
  (θ : ℝ) :
-- imply
  ‖polar_angular θ‖ = 1 := by
-- proof
  simpa [polar_angular, Real.sin_sq_add_cos_sq, Real.norm_eq_abs, sq_abs, neg_sq] using
    Real.Norm.eq.Sqrt (x := polar_angular θ)


-- created on 2026-09-28
