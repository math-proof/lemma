import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.V.eq.Vc.of.Ne0Real_Preimage.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
On a reachable state (`Pr(s[t] = x) ≠ 0` at `θ`), the state value agrees with its closed form near `θ`:
`V θ' γ t x = Vc θ' γ x` for `θ'` in a neighbourhood of `θ`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₁ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₂ : γ ∈ Set.Ico 0 1)
  (t : ℕ)
  (x : S)
  (θ : Θ)
  (h₃ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  (fun θ' => M.V θ' γ t x) =ᶠ[𝓝 θ] fun θ' => M.Vc θ' γ x := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {x})) θ :=
    (Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ t x θ).continuousAt
  filter_upwards [hc.eventually_ne h₃] with θ' h
  exact Random.V.eq.Vc.of.Ne0Real_Preimage.In_Ico (M := M) θ' h₂ t x h


-- created on 2026-10-06
