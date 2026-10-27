import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory Filter ENNReal Topology


namespace MonotoneConvergence

/--
[monotone_convergence_theorem'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MonotoneConvergence.lean)
-/
@[path]
lemma monotone_convergence_theorem'
  [MeasurableSpace α]
  {μ : Measure α}
  {f : ℕ → α → ENNReal}
  {E : Set α}
-- given
  (hf : ∀ n, Measurable (f n))
  (h_mono : Monotone f)
  (_hE : MeasurableSet E) :
-- imply
  Measurable (fun x => ⨆ n, f n x) ∧ (∫⁻ x in E, (⨆ n, f n x) ∂μ = ⨆ n, ∫⁻ x in E, f n x ∂μ) ∧ Tendsto (fun n => ∫⁻ x in E, f n x ∂μ) atTop (𝓝 (∫⁻ x in E, (⨆ n, f n x) ∂μ)) := by
-- proof
  refine ⟨Measurable.iSup hf, lintegral_iSup hf h_mono, ?_⟩
  rw [lintegral_iSup hf h_mono]
  apply tendsto_atTop_iSup
  intro i j hij
  exact lintegral_mono (h_mono hij)

end MonotoneConvergence


-- created on 2026-10-23
