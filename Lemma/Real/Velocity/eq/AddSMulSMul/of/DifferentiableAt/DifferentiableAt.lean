import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Lemma.Real.HasDerivAtPolarRadial_PolarAngular
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Polar product rule for velocity:
\(\vec{v}=\dfrac{d}{dt}(\rho\,\hat{r})=\dot\rho\,\hat{r}+\rho\,\dot\theta\,\hat{\theta}\).
-/
@[path]
private lemma main
  {ρ θ : ℝ → ℝ}
  {t : ℝ}
-- given
  (hρ : DifferentiableAt ℝ ρ t)
  (hθ : DifferentiableAt ℝ θ t) :
-- imply
  velocity (polar_position ρ θ) t =
    deriv ρ t • polar_radial (θ t) +
      ρ t • (deriv θ t • polar_angular (θ t)) := by
-- proof
  have hr : HasDerivAt (polar_radial ∘ θ) (deriv θ t • polar_angular (θ t)) t :=
    (Real.HasDerivAtPolarRadial_PolarAngular (θ t)).scomp t hθ.hasDerivAt
  have h := hρ.hasDerivAt.smul hr
  have hpos : polar_position ρ θ = fun s => ρ s • (polar_radial ∘ θ) s := by
    funext s
    rfl
  simp only [velocity, hpos, Function.comp_def]
  convert h.deriv using 1
  · rfl
  · simp [smul_smul, add_comm]


-- created on 2026-09-28
