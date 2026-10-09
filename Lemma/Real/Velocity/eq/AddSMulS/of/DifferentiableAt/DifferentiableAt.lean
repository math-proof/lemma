import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Product rule for a scaled direction field (notes §5):
\(\vec{v}=\dfrac{d}{dt}(\rho\,\hat{u})=\dot\rho\,\hat{u}+\rho\,\dfrac{d\hat{u}}{dt}\).
-/
@[path]
private lemma main
  {d : ℕ}
  {ρ : ℝ → ℝ}
  {û : Position d}
  {t : ℝ}
-- given
  (hρ : DifferentiableAt ℝ ρ t)
  (hû : DifferentiableAt ℝ û t) :
-- imply
  velocity (fun s => ρ s • û s) t =
    deriv ρ t • û t + ρ t • velocity û t := by
-- proof
  have h := hρ.hasDerivAt.smul hû.hasDerivAt
  simp only [velocity]
  convert h.deriv using 1
  · simp [add_comm]


-- created on 2026-09-28
