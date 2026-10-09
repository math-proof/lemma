import Lemma.Random.Expect_CondDot.eq.Dot_Expect_Cond.of.In_Ico
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
For `γ ∈ [0, 1)` and an arbitrary conditioning set (event) `B` of trajectories, in integral form:
`∫ G[t] d(M θ)[|B] = ∑' k, γ ^ k * ∫ r[t+k] d(M θ)[|B]`.
Derived from `Random.Expect_CondDot.eq.Dot_Expect_Cond.of.In_Ico` (linearity of conditional expectation through the
discounted sum) applied to the event `(· ∈ B) = True`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (B : Set (ℕ → ℝ × S × A))
  (t : ℕ) :
-- imply
  ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω ∂(M θ)[|B] = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|B] := by
-- proof
  set G := (γ ^ (id : ℕ → ℕ)) @ r[t:]
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  have hr : Measurable (fun ω k ↦ r k ω) := Measurable.of_eval fun k => measurable_fst.comp (measurable_pi_apply k)
  have hB : (fun ω ↦ ω ∈ B) ⁻¹' {True} = B := by
    ext ω
    simp
  have h : ∀ k, 𝔼[r : M θ](r (t + k) | (fun ω ↦ ω ∈ B) = True) = ∫ ω, r (t + k) ω ∂(M θ)[|B] := fun k =>
    (Expectation.condEvent_eq_integral hr.aemeasurable (measurable_pi_apply (t + k))).trans (by rw [hB])
  have hG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) := Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have h' := Expect_CondDot.eq.Dot_Expect_Cond.of.In_Ico (M := M) hγ h₁ θ (fun ω ↦ ω ∈ B) True t
  simp only [h] at h'
  simp only [Expectation.asRV_process] at h'
  rwa [Expectation.condEvent_eq_integral hr.aemeasurable hG, hB] at h'


-- created on 2026-10-07
