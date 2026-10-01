import Lemma.Real.HasDerivAtPolarAngular_NegPolarRadial
import sympy.physics.vector.kinematics
import sympy.Basic


/-- Derivative form of \(d\hat{\theta}/d\theta=-\hat{r}\). -/
@[main]
private lemma main
  (θ : ℝ) :
-- imply
  deriv polar_angular θ = -polar_radial θ := by
-- proof
  simpa using (Real.HasDerivAtPolarAngular_NegPolarRadial θ).deriv


-- created on 2026-09-28
