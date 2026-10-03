import Lemma.Random.Expect.Grad.eq.Grad.Expect
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory Topology Random


@[main]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace α]
  {π : Measure Ω} {x : Ω → α} [PSpace π x]
  {f : ℝ → α → ℝ}
  {bound : α → ℝ}
  {s : Set ℝ}
  {θ : ℝ}
-- given
  (hs : s ∈ 𝓝 θ)
  (h_meas : ∀ᶠ θ' in 𝓝 θ, AEStronglyMeasurable (f θ') (π.map x))
  (h_int : Integrable (f θ) (π.map x))
  (h_grad_meas : AEStronglyMeasurable (fun v => deriv (fun θ' => f θ' v) θ) (π.map x))
  (h_bound : ∀ᵐ v ∂(π.map x), ∀ θ' ∈ s, ‖deriv (fun θ' => f θ' v) θ'‖ ≤ bound v)
  (h_bound_int : Integrable bound (π.map x))
  (h_diff : ∀ᵐ v ∂(π.map x), ∀ θ' ∈ s, DifferentiableAt ℝ (fun θ' => f θ' v) θ') :
-- imply
  deriv (fun θ' => 𝔼[x: π](f θ' x)) θ = 𝔼[x: π](deriv (fun θ' => f θ' x) θ) := by
-- proof
  exact (Expect.Grad.eq.Grad.Expect hs h_meas h_int h_grad_meas h_bound h_bound_int h_diff).symm


-- created on 2026-10-01
