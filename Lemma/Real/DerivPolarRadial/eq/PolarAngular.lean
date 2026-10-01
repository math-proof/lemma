import Lemma.Real.HasDerivAtPolarRadial_PolarAngular
import sympy.physics.vector.kinematics
import sympy.Basic


/-- Derivative form of \(d\hat{r}/d\theta=\hat{\theta}\). -/
@[main]
private lemma main
  (θ : ℝ) :
-- imply
  deriv polar_radial θ = polar_angular θ := by
-- proof
  simpa using (Real.HasDerivAtPolarRadial_PolarAngular θ).deriv


-- created on 2026-09-28
