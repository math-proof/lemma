import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Lemma.Real.HasDerivAtPolarAngular_NegPolarRadial
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Chain rule for the angular unit along a path:
\(\dfrac{d}{dt}\hat{\theta}(\theta(t))=-\dot\theta\,\hat{r}(\theta(t))\).
-/
@[path]
private lemma main
  {θ : ℝ → ℝ}
  {t : ℝ}
-- given
  (hθ : DifferentiableAt ℝ θ t) :
-- imply
  HasDerivAt (polar_angular ∘ θ) (-(deriv θ t) • polar_radial (θ t)) t := by
-- proof
  have h := (Real.HasDerivAtPolarAngular_NegPolarRadial (θ t)).scomp t hθ.hasDerivAt
  simpa [smul_neg, neg_smul] using h


-- created on 2026-09-28
