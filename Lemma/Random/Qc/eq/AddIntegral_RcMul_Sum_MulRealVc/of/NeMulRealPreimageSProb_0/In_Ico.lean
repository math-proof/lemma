import Lemma.Random.Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico
import Lemma.Random.Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
On a reachable state-action at time 0:
`Qc θ γ x u = ∫ ρ, clip ρ ∂reward(x,u) + γ * ∑ y, T(x,u,y) * Vc θ γ y`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (x : S)
  (u : A)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₂ : (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x}) * M.policy.prob θ x u ≠ 0)
  (hV : ∀ y, (M.env.trans (x, u)).real {y} ≠ 0 →
      (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {y}) ≠ 0) :
-- imply
  M.Qc θ γ x u =
    (∫ ρ, clip ρ (-M.env.R) M.env.R ∂(M.env.reward (x, u))) +
      γ * ∑ y, (M.env.trans (x, u)).real {y} * M.Vc θ γ y := by
-- proof
  let r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  let s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  let a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have h₁ : ∀ t, (· t) = (r t, s t, a t) := fun t => funext fun ω => rfl
  have hP : (M θ).real (s 0 ⁻¹' {x}) * M.policy.prob θ x u ≠ 0 := h₂
  have hsum :
      (∑ y : S, (M.env.trans (x, u)).real {y} *
        ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y)) =
      (∑ y : S, (M.env.trans (x, u)).real {y} * M.Vc θ γ y) := by
    refine Finset.sum_congr rfl fun (y : S) _ => ?_
    by_cases hy : (M.env.trans (x, u)).real {y} = 0
    · simp [hy]
    · rw [Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico (M := M) h₀ θ y (hV y hy)]
  unfold Model.Qc
  have hQ :=
    Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico
      (M := M) θ 0 x u h₀ h₁ hP
  refine Eq.trans hQ ?_
  refine congrArg (fun z : ℝ => (∫ ρ, clip ρ (-M.env.R) M.env.R ∂(M.env.reward (x, u))) + γ * z) hsum


-- created on 2026-10-20
