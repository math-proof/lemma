import Mathlib
import sympy.Basic
import sympy.atlas.Dynamics.Ergodic.Kingman
open MeasureTheory Filter Topology
open MathlibExt.Dynamics.Ergodic.KingmanWanted


/--
[kingman_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/Kingman.lean)
-/
@[path]
private lemma kingman_subadditive_eq
  [MeasurableSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ]
  {T : α → α}
  {f : ℕ → α → ℝ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf_meas : ∀ n, Measurable (f n))
  (hf_int : ∀ n, Integrable (f n) μ)
  (hf_nonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x)
  (hf_zero : ∀ᵐ x ∂μ, f 0 x = 0)
  (hf_subadd : ∀ m n, ∀ᵐ x ∂μ, f (m + n) x ≤ f m x + f n ((T^[m]) x)) :
-- imply
  ∃ g : α → ℝ, Integrable g μ ∧ (∀ᵐ x ∂μ, g (T x) = g x) ∧
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => f n x / (n : ℝ)) atTop (nhds (g x)) := by
-- proof
  apply MathlibExt.Dynamics.Ergodic.KingmanWanted.kingman_subadditive hT f hf_meas hf_int hf_nonneg hf_zero hf_subadd


-- created on 2026-10-20
