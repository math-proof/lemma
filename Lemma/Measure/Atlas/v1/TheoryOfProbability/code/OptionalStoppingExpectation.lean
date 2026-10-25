import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.TheoryOfProbability.code.OptionalStoppingExpectation
open MeasureTheory
open scoped ProbabilityTheory


namespace MeasureTheory

/--
[Submartingale.expected_stoppedValue_mono_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/OptionalStoppingExpectation.lean)
-/
@[path]
lemma Submartingale.expected_stoppedValue_mono_real
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  {𝒢 : Filtration ℕ m0}
  {π : Ω → ℕ∞}
  [SigmaFiniteFiltration μ 𝒢]
  {N : ℕ}
-- given
  (hf : Submartingale f 𝒢 μ)
  (hτ : IsStoppingTime 𝒢 τ)
  (hπ : IsStoppingTime 𝒢 π)
  (hle : τ ≤ π)
  (hbdd : ∀ ω, π ω ≤ N) :
-- imply
  μ[stoppedValue f τ] ≤ μ[stoppedValue f π] := by
-- proof
  rw [← sub_nonneg, ← integral_sub', stoppedValue_sub_eq_sum' hle hbdd]
  · simp only [Finset.sum_apply]
    have hmeas : ∀ i, MeasurableSet[𝒢 i] {ω : Ω | τ ω ≤ i ∧ ↑i < π ω} := by
      intro i
      refine (hτ i).inter ?_
      convert (hπ i).compl using 1
      ext x
      simp; rfl
    rw [integral_finset_sum]
    · refine Finset.sum_nonneg fun i _ => ?_
      rw [integral_indicator (𝒢.le _ _ (hmeas _)), integral_sub', sub_nonneg]
      · exact hf.setIntegral_le (Nat.le_succ i) (hmeas _)
      · exact (hf.integrable _).integrableOn
      · exact (hf.integrable _).integrableOn
    · intro i _
      exact ((hf.integrable _).sub (hf.integrable _)).indicator
        (𝒢.le _ _ (hmeas _))
  · exact hf.integrable_stoppedValue hπ hbdd
  · exact hf.integrable_stoppedValue hτ (fun ω => (hle ω).trans (hbdd ω))

end MeasureTheory

namespace MeasureTheory

/--
[Supermartingale.expected_stoppedValue_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/OptionalStoppingExpectation.lean)
-/
@[path]
lemma Supermartingale.expected_stoppedValue_le
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  {𝒢 : Filtration ℕ m0}
  [SigmaFiniteFiltration μ 𝒢]
  {N : ℕ}
-- given
  (hf : Supermartingale f 𝒢 μ)
  (hτ : IsStoppingTime 𝒢 τ)
  (hbdd : ∀ ω, τ ω ≤ N) :
-- imply
  μ[stoppedValue f τ] ≤ μ[f 0] := by
-- proof
  have hsub : Submartingale (-f) 𝒢 μ := hf.neg
  have h0 : ∀ ω, (fun _ : Ω => (0 : ℕ∞)) ω ≤ τ ω := fun ω => zero_le _
  have key := hsub.expected_stoppedValue_mono_real (isStoppingTime_const 𝒢 0) hτ h0 hbdd
  simp only [stoppedValue_const] at key
  have eq1 : μ[stoppedValue (-f) τ] = -μ[stoppedValue f τ] := by
    simp only [integral_neg, stoppedValue, Pi.neg_apply]
  have eq2 : μ[(-f) 0] = -μ[f 0] := integral_neg _
  rw [eq1, eq2] at key
  linarith

end MeasureTheory


-- created on 2026-10-23
