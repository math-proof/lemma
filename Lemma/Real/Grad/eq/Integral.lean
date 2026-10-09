import Mathlib.Analysis.Calculus.ParametricIntegral
import sympy.Basic
open MeasureTheory Topology


/--
| attributes | lemma |
| :---: | :---: |
| path | Real.Grad.eq.Integral |
| comm | Real.Integral.eq.Grad |
-/
@[path, comm]
private lemma main
  {f : ℝ → ℝ → ℝ}
  {bound : ℝ → ℝ}
  {s : Set ℝ}
  {x : ℝ}
-- given
  (hs : s ∈ 𝓝 x)
  (h_meas : ∀ᶠ x' in 𝓝 x, AEStronglyMeasurable (f x') volume)
  (h_int : Integrable (f x) volume)
  (h_grad_meas : AEStronglyMeasurable (fun y => deriv (f · y) x) volume)
  (h_bound : ∀ᵐ y, ∀ x' ∈ s, ‖deriv (f · y) x'‖ ≤ bound y)
  (h_bound_int : Integrable bound volume)
  (h_diff : ∀ᵐ y, ∀ x' ∈ s, DifferentiableAt ℝ (f · y) x') :
-- imply
  deriv (fun x' => ∫ y, f x' y) x = ∫ y, deriv (f · y) x := by
-- proof
  obtain ⟨_, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs h_meas h_int h_grad_meas h_bound h_bound_int (h_diff.mono fun y hy x' hx' => (hy x' hx').hasDerivAt)
  exact h.deriv


-- created on 2026-10-01
