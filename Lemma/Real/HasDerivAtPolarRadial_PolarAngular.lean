import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import sympy.physics.vector.kinematics
import sympy.Basic
open scoped ENNReal


/--
\(d\hat{r}/d\theta=\hat{\theta}\): the polar radial unit vector is differentiable
with derivative the angular unit vector (geometric limit \(\Delta\hat{r}\approx\hat{\theta}\,\Delta\theta\)).
-/
@[main]
private lemma main
  (θ : ℝ) :
-- imply
  HasDerivAt polar_radial (polar_angular θ) θ := by
-- proof
  let e := (WithLp.linearEquiv (2 : ℝ≥0∞) ℝ (Fin 2 → ℝ)).toContinuousLinearEquiv
  have hpi :
      HasDerivAt (fun φ : ℝ => (![Real.cos φ, Real.sin φ] : Fin 2 → ℝ))
        (![(-Real.sin θ), Real.cos θ] : Fin 2 → ℝ) θ := by
    apply (hasDerivAt_pi (ι := Fin 2)).2
    intro i
    fin_cases i
    · simpa using Real.hasDerivAt_cos θ
    · simpa using Real.hasDerivAt_sin θ
  have h := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt θ hpi
  change HasDerivAt (fun φ => e.symm ![Real.cos φ, Real.sin φ])
    (e.symm ![-Real.sin θ, Real.cos θ]) θ
  exact h


-- created on 2026-09-28
