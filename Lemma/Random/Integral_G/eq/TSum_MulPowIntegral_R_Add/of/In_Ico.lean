import Lemma.Random.Expect_CondDot.eq.Dot_Expect_Cond.of.In_Ico
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
For `γ ∈ [0, 1)` and an arbitrary conditioning set (event) `B` of trajectories, in integral form:
`∫ G[t] d(M θ)[|B] = ∑' k, γ ^ k * ∫ r[t+k] d(M θ)[|B]`.
Derived from `Random.Expect_CondDot.eq.Dot_Expect_Cond.of.In_Ico` (linearity of conditional expectation through the
discounted sum) applied to the event `(· ∈ B) = True`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (B : Set (ℕ → ℝ × S × A))
  (t : ℕ) :
-- imply
  ∫ ω, G γ t ω ∂(M θ)[|B] = ∑' k, γ ^ k * ∫ ω, reward (t + k) ω ∂(M θ)[|B] := by
-- proof
  have hr : Measurable (fun ω k ↦ reward (S := S) (A := A) k ω) := measurable_pi_lambda _ fun k => measurable_fst.comp (measurable_pi_apply k)
  have hB : (fun ω ↦ ω ∈ B) ⁻¹' {True} = B := by
    ext ω
    simp
  have h : ∀ k, 𝔼[reward : M θ](reward (t + k) | (fun ω ↦ ω ∈ B) = True) = ∫ ω, reward (t + k) ω ∂(M θ)[|B] := fun k =>
    (Expectation.condEvent_eq_integral hr.aemeasurable (measurable_pi_apply (t + k))).trans (by rw [hB])
  have hG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) := Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have h' := Expect_CondDot.eq.Dot_Expect_Cond.of.In_Ico (M := M) hγ θ (fun ω ↦ ω ∈ B) True t
  simp only [h] at h'
  simp only [Expectation.asRV_process] at h'
  rw [Expectation.condEvent_eq_integral hr.aemeasurable hG, hB] at h'
  exact h'


-- created on 2026-10-07
