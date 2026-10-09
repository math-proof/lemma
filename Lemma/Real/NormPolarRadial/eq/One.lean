import Lemma.Real.Norm.eq.Sqrt
import sympy.physics.vector.kinematics
import sympy.Basic


/-- Polar radial unit vector has length one: \(|\hat{r}|=1\). -/
@[path]
private lemma main
  (θ : ℝ) :
-- imply
  ‖polar_radial θ‖ = 1 := by
-- proof
  simpa [polar_radial, Real.cos_sq_add_sin_sq, Real.norm_eq_abs, sq_abs] using
    Real.Norm.eq.Sqrt (x := polar_radial θ)


-- created on 2026-09-28
