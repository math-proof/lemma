import sympy.stats.policy_trajectory.gradient
import sympy.vector.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Random.Fderiv.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Policy-gradient recursion for the model value functions on a reachable state x (h₃ : Pr(s[t] = x) ≠ 0):
∇V(t, x) = ∑ u, Q(t, x, u) • ∇π(u | x) + γ • ∑ y, P1(x, y) • ∇V(t+1, y),
where V = M.V, Q = M.Q are the state / action values of the trajectory model, P1 θ x y = Pr(s[t+1] = y | s[t] = x),
and θ ↦ π_θ(u | x) is differentiable (h₁) with a bounded gradient (h₂).
Gradient (Riesz representative) form of `Random.Fderiv.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {x : S}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₂ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₃ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  ∇[θ] M.V θ γ t x =
    ∑ u, M.Q θ γ t x u • ∇[θ] M.pol.prob θ x u +
      γ • ∑ y, M.P1 θ x y • ∇[θ] M.V θ γ (t + 1) y := by
-- proof
  classical
  simpa [gradient, map_add, map_smul, map_sum] using
    congrArg (InnerProductSpace.toDual ℝ Θ).symm
      (Fderiv.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob t x θ h₁ h₂ h₀ h₃)


-- created on 2026-10-06