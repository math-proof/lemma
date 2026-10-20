import sympy.stats.policy_trajectory.gradient
import Lemma.Random.V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico
import Lemma.Random.Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
On a state reachable at times t and 0, the time-indexed value equals its time-free form:
`M.V θ γ t x = M.Vc θ γ x`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₂ : (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω t).2.1) ⁻¹' {x}) ≠ 0)
  (h₃ : (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x}) ≠ 0) :
-- imply
  M.V θ γ t x = M.Vc θ γ x := by
-- proof
  let r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  let s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  let a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have h₁ : ∀ t, (· t) = (r t, s t, a t) := fun t => funext fun ω => rfl
  have h₂' : (M θ).real (s t ⁻¹' {x}) ≠ 0 := h₂
  refine Eq.trans ?_ (Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico (M := M) h₀ θ x h₃).symm
  unfold Model.V
  exact V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico (M := M) (r := r) (s := s) (a := a)
    θ t x h₀ h₁ h₂'


-- created on 2026-10-06
-- updated on 2026-10-20
