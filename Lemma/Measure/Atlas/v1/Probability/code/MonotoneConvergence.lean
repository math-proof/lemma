import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory Filter ENNReal Topology


/--
[monotone_convergence_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MonotoneConvergence.lean)
-/
@[path]
lemma monotone_convergence_theorem
  {m : MeasurableSpace α}
  {μ : Measure α}
  {f : ℕ → α → ENNReal}
  {g : α → ENNReal}
-- given
  (hf_meas : ∀ n, Measurable (f n))
  (hf_mono : Monotone f)
  (hf_lim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
-- imply
  Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, g x ∂μ)) := by
-- proof
  have hg : g = fun x => ⨆ n, f n x := by
    ext x
    exact tendsto_nhds_unique (hf_lim x)
      (tendsto_atTop_iSup (fun n m hnm => hf_mono hnm x))
  rw [hg, lintegral_iSup hf_meas hf_mono]
  exact tendsto_atTop_iSup fun n m hnm => lintegral_mono (hf_mono hnm)


-- created on 2026-10-23
