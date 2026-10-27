import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory Filter Topology


namespace DominatedConvergence

/--
[dominated_convergence_integrable_and_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DominatedConvergence.lean)
-/
@[path]
lemma dominated_convergence_integrable_and_tendsto
  {m : MeasurableSpace α}
  {μ : MeasureTheory.Measure α}
  {F : ℕ → α → ℝ}
  {f : α → ℝ}
  {g : α → ℝ}
-- given
  (hF_integrable : ∀ n, Integrable (F n) μ)
  (hg_integrable : Integrable g μ)
  (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ g a)
  (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
-- imply
  Integrable f μ ∧ Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) := by
-- proof
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) μ :=
    fun n => (hF_integrable n).aestronglyMeasurable
  constructor
  ·
    have hf_meas : AEStronglyMeasurable f μ :=
      aestronglyMeasurable_of_tendsto_ae _ hF_meas h_lim
    have h_bound_f : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a := by
      filter_upwards [h_lim, ae_all_iff.mpr h_bound] with a ha_lim ha_bound
      exact le_of_tendsto' ha_lim.norm ha_bound
    exact hg_integrable.mono' hf_meas h_bound_f
  ·
    exact MeasureTheory.tendsto_integral_of_dominated_convergence g hF_meas hg_integrable
      h_bound h_lim

end DominatedConvergence


-- created on 2026-10-23
