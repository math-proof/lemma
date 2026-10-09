import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import sympy.physics.vector.kinematics
import sympy.Basic


/--
The Kepler / Binet ansatz satisfies \(w''+w=Cm/J^2\).
-/
@[path]
private lemma main
  (A C m J ψ : ℝ)
-- given
  (_hJ : J ≠ 0) :
-- imply
  ∀ φ,
    deriv (deriv (fun ξ => A * Real.cos (ξ + ψ) + C * m / J ^ 2)) φ +
        (A * Real.cos (φ + ψ) + C * m / J ^ 2) =
      C * m / J ^ 2 := by
-- proof
  intro φ
  set w : ℝ → ℝ := fun ξ => A * Real.cos (ξ + ψ) + C * m / J ^ 2
  have hw' : ∀ ξ, HasDerivAt w (-A * Real.sin (ξ + ψ)) ξ := by
    intro ξ
    have hcomp0 :=
      (Real.hasDerivAt_cos (ξ + ψ)).comp ξ ((hasDerivAt_id ξ).add_const ψ)
    have hcomp : HasDerivAt (fun ξ => Real.cos (ξ + ψ)) (-Real.sin (ξ + ψ)) ξ :=
      hcomp0.congr_deriv (by simp)
    have hA : HasDerivAt (fun ξ => A * Real.cos (ξ + ψ)) (-A * Real.sin (ξ + ψ)) ξ :=
      (hcomp.const_mul A).congr_deriv (by ring)
    exact (hA.add (hasDerivAt_const ξ (C * m / J ^ 2))).congr_deriv (by simp)
  have hder1 : deriv w = fun ξ => -A * Real.sin (ξ + ψ) := by
    ext ξ
    exact (hw' ξ).deriv
  have hw'' : HasDerivAt (deriv w) (-A * Real.cos (φ + ψ)) φ := by
    rw [hder1]
    have hcomp0 :=
      (Real.hasDerivAt_sin (φ + ψ)).comp φ ((hasDerivAt_id φ).add_const ψ)
    have hcomp : HasDerivAt (fun ξ => Real.sin (ξ + ψ)) (Real.cos (φ + ψ)) φ :=
      hcomp0.congr_deriv (by simp)
    exact (hcomp.const_mul (-A)).congr_deriv (by ring)
  have : deriv (deriv w) φ = -A * Real.cos (φ + ψ) := hw''.deriv
  change deriv (deriv w) φ + w φ = C * m / J ^ 2
  rw [this]
  simp only [w]
  ring


-- created on 2026-09-29
