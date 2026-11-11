import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory Filter Topology


/--
[MeasureTheory.tendsto_integral_of_bounded_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BoundedConvergence.lean)
-/
@[path]
lemma MeasureTheory.tendsto_integral_of_bounded_convergence
  {m : MeasurableSpace α}
  {μ : Measure α}
  [IsProbabilityMeasure μ]
  [NormedAddCommGroup G]
  [NormedSpace ℝ G]
  {F : ℕ → α → G}
  {f : α → G}
  {C : ℝ}
-- given
  (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
  (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ C)
  (h_lim : TendstoInMeasure μ F atTop f) :
-- imply
  Tendsto (fun n ↦ ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) := by
-- proof
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have h_lim_ns : TendstoInMeasure μ (fun n ↦ F (ns n)) atTop f :=
    fun ε hε ↦ (h_lim ε hε).comp hns
  obtain ⟨ms, -, hms_ae⟩ := h_lim_ns.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  exact tendsto_integral_of_dominated_convergence (fun _ ↦ C)
    (fun n ↦ hF_meas (ns (ms n)))
    (integrable_const C)
    (fun n ↦ h_bound (ns (ms n)))
    hms_ae


-- created on 2026-10-23
