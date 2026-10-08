import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
The discounted return `G[t]` is integrable under the trajectory model.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (t : ℕ)
  (h₁ : ∀ t, (· t) = (r t, s t, a t)) :
-- imply
  Integrable (G r γ t) (M θ) := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  have hm : AEStronglyMeasurable (G r γ t) (M θ) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n ω => ∑ k ∈ Finset.range n, γ ^ k * (ω (t + k)).1) (fun n => ?_) ?_
    · exact (Finset.measurable_fun_sum _ fun k _ =>
        (measurable_fst.comp (measurable_pi_apply (t + k))).const_mul (γ ^ k)).aestronglyMeasurable
    · exact (Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico (M := M) (r := fun t ω ↦ (ω t).1) (s := fun t ω ↦ (ω t).2.1) (a := fun t ω ↦ (ω t).2.2) h₀ (fun _ ↦ rfl) θ t).mono fun ω h => h.1.tendsto_sum_nat
  exact Integrable.of_bound hm _ ((Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico (M := M) (r := fun t ω ↦ (ω t).1) (s := fun t ω ↦ (ω t).2.1) (a := fun t ω ↦ (ω t).2.2) h₀ (fun _ ↦ rfl) θ t).mono fun ω h => h.2)


-- created on 2026-10-06
