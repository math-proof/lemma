import sympy.stats.policy_trajectory.gradient
import Lemma.Random.V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
On a state reachable at time 0 (ℙ(s[0] = y) ≠ 0), the time-free value equals the
kernel series:
Vc θ γ y = ∑' k, γ ^ k * ∫ z, Kf θ (clip ·.1) k z ∂(stageK θ y).
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (y : S)
  (hP : (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {y}) ≠ 0) :
-- imply
  M.Vc θ γ y = ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y) := by
-- proof
  let r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  let s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  let a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have h₁ : ∀ t, (· t) = (r t, s t, a t) := fun t => funext fun ω => rfl
  have hP' : (M θ).real (s 0 ⁻¹' {y}) ≠ 0 := hP
  unfold Model.Vc Model.V
  exact V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico (M := M) (r := r) (s := s) (a := a)
    θ 0 y h₀ h₁ hP'


-- created on 2026-10-11
-- updated on 2026-10-20
