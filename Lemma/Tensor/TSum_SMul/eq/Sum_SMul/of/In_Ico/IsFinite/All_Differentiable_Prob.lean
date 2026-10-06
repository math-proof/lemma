import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Random.Integral_R.eq.Sum_MulRealWRc
import Lemma.Tensor.Differentiable_Vc.of.In_Ico.IsFinite.All_Differentiable_Prob
import Lemma.Tensor.GetTSum_SMul.of.In_Ico.IsFinite.All_Differentiable_Prob
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


private lemma obj_eq [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) :
    ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ) = ∑ x, M.env.init.real {x} * M.Vc θ γ x := by
  simp_rw [Random.Integral_R.eq.Sum_MulRealWRc (M := M) θ]
  exact tsum_pull _ _ (fun x => summable_W M θ hγ x)

/--
`∇ ∑' t, γ ^ t * 𝔼[r[t]] = ∑ x, Pr(s[0] = x) • ∇ Vc(x)`
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
  (θ : Θ) :
-- imply
  ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
    ∑ x, M.env.init.real {x} • fderiv ℝ (fun θ => M.Vc θ γ x) θ := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  rw [← (Tensor.GetTSum_SMul.of.In_Ico.IsFinite.All_Differentiable_Prob (M := M) h₀ h₁ h₂ θ).fderiv]
  have e : (fun θ => ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ)) =
      fun θ => ∑ x, M.env.init.real {x} * M.Vc θ γ x := funext fun θ => obj_eq M θ h₂
  rw [e, fderiv_fun_sum fun x _ => ((Tensor.Differentiable_Vc.of.In_Ico.IsFinite.All_Differentiable_Prob (M := M) h₀ h₁ h₂ x) θ).const_mul _]
  exact Finset.sum_congr rfl fun x _ => fderiv_const_mul ((Tensor.Differentiable_Vc.of.In_Ico.IsFinite.All_Differentiable_Prob (M := M) h₀ h₁ h₂ x) θ) _


-- created on 2026-10-06
