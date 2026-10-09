import sympy.stats.policy_trajectory.continuous
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Random.Vk.eq.Sum_MulProbQk.of.In_Ico.All_Measurable_Prob
import Lemma.Random.DifferentiableAt.Fderiv.eq.SMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob
open MeasureTheory PolicyGradient Random


/--
gradient of the Bellman equation for the closed-form value function on a general (e.g. continuous) state space:
`fderiv Vk(x) = ∑ u, Qk(x, u) • fderiv π(u | x) + γ • ∑ u, π(u | x) • ∫ y, fderiv Vk(y) ∂T(· | x, u)`.
Continuous-state counterpart of `Tensor.Fderiv.eq.AddSum_SMulSMul.of.In_Ico.GtInftySup.All_Differentiable_Prob`:
the next-state sum `∑ y, P1(x, y) • fderiv Vc(y)` becomes the policy mixture of the transition integrals.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ] [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₁ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₂ : γ ∈ Set.Ico 0 1)
  (h₃ : ∀ θ u, Measurable (fun x => M.pol.prob θ x u))
  (x : S)
  (θ : Θ) :
-- imply
  fderiv ℝ (fun θ => M.Vk θ γ x) θ =
    ∑ u, M.Qk θ γ x u • fderiv ℝ (fun θ => M.pol.prob θ x u) θ +
      γ • ∑ u, M.pol.prob θ x u • ∫ y, fderiv ℝ (fun θ => M.Vk θ γ y) θ ∂(M.env.trans (x, u)) := by
-- proof
  have hb : (fun θ => M.Vk θ γ x) = fun θ => ∑ u, M.pol.prob θ x u * M.Qk θ γ x u :=
    funext fun θ => Vk.eq.Sum_MulProbQk.of.In_Ico.All_Measurable_Prob (M := M) h₃ h₂ θ x
  have hQ := fun u => DifferentiableAt.Fderiv.eq.SMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃ x u θ
  rw [hb, fderiv_fun_sum fun u _ => ((h₀ x u) θ).fun_mul (hQ u).1]
  simp_rw [fderiv_fun_mul ((h₀ _ _) θ) (hQ _).1, (hQ _).2]
  rw [Finset.sum_add_distrib, add_comm, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_comm]


-- created on 2026-10-07
