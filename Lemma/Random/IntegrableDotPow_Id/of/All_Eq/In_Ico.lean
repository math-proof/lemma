import Lemma.Random.All_And_LeNormExtDotPow_Id.of.All_Eq_Joint.In_Ico
open MeasureTheory Finset Filter PolicyGradient PolicyGradient.Model Random


/--
The discounted return `G[t]` is integrable under the trajectory model.
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
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
-- imply
  Integrable ((γ ^ (id : ℕ → ℕ)) @ r[t:]) (M θ) := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  refine Integrable.of_bound ?_ ((1 - γ)⁻¹ * |M.env.R|) ?_
  ·
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n ω => ∑ k ∈ range n, γ ^ k * (ω (t + k)).1) (fun n => ?_) ?_
    ·
      apply (measurable_fun_sum _ fun k _ =>
        (measurable_fst.comp (measurable_pi_apply (t + k))).const_mul (γ ^ k)).aestronglyMeasurable
    ·
      apply (All_And_LeNormExtDotPow_Id.of.All_Eq_Joint.In_Ico (M := M) (r := fun t ω ↦ (ω t).1)
        (s := fun t ω ↦ (ω t).2.1) (a := fun t ω ↦ (ω t).2.2) h₀ (fun _ ↦ rfl) θ t).mono
      intro ω h
      apply h.1.tendsto_sum_nat
  ·
    apply (All_And_LeNormExtDotPow_Id.of.All_Eq_Joint.In_Ico (M := M) (r := fun t ω ↦ (ω t).1)
      (s := fun t ω ↦ (ω t).2.1) (a := fun t ω ↦ (ω t).2.2) h₀ (fun _ ↦ rfl) θ t).mono
    intro ω h
    apply h.2


-- created on 2026-10-06
-- updated on 2026-10-12
