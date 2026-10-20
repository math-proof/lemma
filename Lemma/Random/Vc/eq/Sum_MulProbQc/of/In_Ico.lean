import Lemma.Random.Integral.eq.Sum_MulRealEq
import Lemma.Random.Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico
import Lemma.Random.TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico
import Lemma.Random.Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico
import Lemma.Random.W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
Bellman equation of the time-free values on a reachable state:
`Vc θ γ x = ∑ u, π_θ(u | x) * Qc θ γ x u`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (x : S)
  (hP : (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x}) ≠ 0) :
-- imply
  M.Vc θ γ x = ∑ u, M.policy.prob θ x u * M.Qc θ γ x u := by
-- proof
  let r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  let s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  let a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have h₁ : ∀ t, (· t) = (r t, s t, a t) := fun t => funext fun ω => rfl
  rw [Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico (M := M) h₀ θ x hP,
    TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico (M := M) h₀ θ x]
  have hKf0 : M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 0 =
      fun z ↦ clip z.1 (-M.env.R) M.env.R := rfl
  simp_rw [hKf0]
  rw [W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable (M := M)
    (Random.StronglyMeasurableClip (M := M)) (NormClip.le.AbsR (M := M)) θ x]
  have hterm : ∀ u, M.policy.prob θ x u *
      ((∫ ρ, clip (ρ, x, u).1 (-M.env.R) M.env.R ∂(M.env.reward (x, u))) +
        γ * ∑ y, (M.env.trans (x, u)).real {y} *
          ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y)) =
      M.policy.prob θ x u * M.Qc θ γ x u := by
    intro u
    by_cases hu : M.policy.prob θ x u = 0
    · simp [hu]
    · have hPu : (M θ).real (s 0 ⁻¹' {x}) * M.policy.prob θ x u ≠ 0 :=
        mul_ne_zero hP hu
      have hQ :=
        Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico
          (M := M) θ 0 x u h₀ h₁ hPu
      rw [← hQ]
      unfold Model.Qc Model.Q
      -- both sides: π * Expectation.condEvent … ; align RV/coords
      congr 1
  have hreshape :
      ∑ u, M.policy.prob θ x u * ∫ ρ, clip (ρ, x, u).1 (-M.env.R) M.env.R ∂(M.env.reward (x, u)) +
          γ * ∑ u, M.policy.prob θ x u * ∑ y, (M.env.trans (x, u)).real {y} *
            ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y) =
        ∑ u, M.policy.prob θ x u *
          ((∫ ρ, clip (ρ, x, u).1 (-M.env.R) M.env.R ∂(M.env.reward (x, u))) +
            γ * ∑ y, (M.env.trans (x, u)).real {y} *
              ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y)) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    refine congrArg₂ (· + ·) rfl ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  exact hreshape.trans (Finset.sum_congr rfl fun u _ => hterm u)


-- created on 2026-10-06
-- updated on 2026-10-20
