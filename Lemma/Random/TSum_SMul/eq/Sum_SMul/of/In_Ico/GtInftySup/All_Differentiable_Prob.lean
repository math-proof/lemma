import Lemma.Random.Differentiable_FunVc.of.InIco0.GtInftySup_Norm.All_All_Differentiable_FunPolProb
import Lemma.Random.GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Real.TSum_MulPowSum_Mul.eq.Sum_Mul_TSum_MulPow.of.All_Summable_MulPow
import Lemma.Random.Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


private lemma obj_eq
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (M : Model Θ S A)
  (θ : Θ)
  {γ : ℝ}
  (hγ : γ ∈ Set.Ico 0 1)
  (hP : ∀ x, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x}) ≠ 0) :
  ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ) = ∑ x, M.env.init.real {x} * M.Vc θ γ x := by
  simp_rw [Integral_R.eq.Sum_MulRealWRc (M := M) h₁ θ]
  rw [TSum_MulPowSum_Mul.eq.Sum_Mul_TSum_MulPow.of.All_Summable_MulPow _
    (fun x => Summable_MulPowWRc.of.In_Ico (M := M) hγ θ x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico (M := M) hγ θ x (hP x)]

/--
`∇ ∑' t, γ ^ t * 𝔼[r[t]] = ∑ x, ℙ(s[0] = x) • ∇ Vc(x)`
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (θ : Θ)
  (h₄ : ∀ θ x, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x}) ≠ 0) :
-- imply
  ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
    ∑ x, M.env.init.real {x} • fderiv ℝ (fun θ => M.Vc θ γ x) θ := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₃
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  rw [← (GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃ θ).fderiv]
  have e : (fun θ => ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ)) =
      fun θ => ∑ x, M.env.init.real {x} * M.Vc θ γ x := funext fun θ => obj_eq h₁ M θ h₀ (h₄ θ)
  rw [e, fderiv_fun_sum fun x _ =>
    ((Differentiable_FunVc.of.InIco0.GtInftySup_Norm.All_All_Differentiable_FunPolProb (M := M) h₂ h₃ h₀ x
      (fun θ => h₄ θ x)) θ).const_mul _]
  exact Finset.sum_congr rfl fun x _ =>
    fderiv_const_mul
      ((Differentiable_FunVc.of.InIco0.GtInftySup_Norm.All_All_Differentiable_FunPolProb (M := M) h₂ h₃ h₀ x
        (fun θ => h₄ θ x)) θ) _


-- created on 2026-10-06
-- updated on 2026-10-20
