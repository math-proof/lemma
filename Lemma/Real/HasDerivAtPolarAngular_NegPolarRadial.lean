import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import sympy.physics.vector.kinematics
import sympy.Basic
open scoped ENNReal


/--
\(d\hat{\theta}/d\theta=-\hat{r}\): the polar angular unit vector is differentiable
with derivative \(-\hat{r}\) (geometric limit \(\Delta\hat{\theta}\approx-\hat{r}\,\Delta\theta\)).
-/
@[main]
private lemma main
  (θ : ℝ) :
-- imply
  HasDerivAt polar_angular (-polar_radial θ) θ := by
-- proof
  let e := (WithLp.linearEquiv (2 : ℝ≥0∞) ℝ (Fin 2 → ℝ)).toContinuousLinearEquiv
  have hsin : HasDerivAt (fun φ : ℝ => -Real.sin φ) (-Real.cos θ) θ :=
    (Real.hasDerivAt_sin θ).neg
  have hcos : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have hpi :
      HasDerivAt (fun φ : ℝ => (![(-Real.sin φ), Real.cos φ] : Fin 2 → ℝ))
        (![(-Real.cos θ), -Real.sin θ] : Fin 2 → ℝ) θ := by
    apply (hasDerivAt_pi (ι := Fin 2)).2
    intro i
    fin_cases i
    · exact hsin
    · exact hcos
  have h := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt θ hpi
  have hneg : -polar_radial θ = WithLp.toLp 2 ![-Real.cos θ, -Real.sin θ] := by
    ext i
    fin_cases i <;>
      simp [polar_radial, PiLp.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
  rw [show polar_angular = fun φ => e.symm ![-Real.sin φ, Real.cos φ] from rfl, hneg,
    show WithLp.toLp 2 ![-Real.cos θ, -Real.sin θ] = e.symm ![-Real.cos θ, -Real.sin θ] from rfl]
  exact h


-- created on 2026-09-28
