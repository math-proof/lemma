import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Lemma.Real.HasDerivAtPolarRadial_PolarAngular
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Chain rule along a path (notes §9):
\(\dfrac{d}{dt}\hat{r}(\theta(t))=\dot\theta\,\hat{\theta}(\theta(t))\).
-/
@[main]
private lemma main
  {θ : ℝ → ℝ}
  {t : ℝ}
-- given
  (hθ : DifferentiableAt ℝ θ t) :
-- imply
  HasDerivAt (polar_radial ∘ θ) (deriv θ t • polar_angular (θ t)) t := by
-- proof
  exact (Real.HasDerivAtPolarRadial_PolarAngular (θ t)).scomp t hθ.hasDerivAt


-- created on 2026-09-28
