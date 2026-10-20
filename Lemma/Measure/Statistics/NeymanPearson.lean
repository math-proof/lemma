import Mathlib
import sympy.Basic
import sympy.atlas.Probability.Statistics.NeymanPearson
open MeasureTheory
open MathlibExt.Probability.Statistics.NeymanPearson


/--
[neyman_pearson_dominated_two_simple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Statistics/NeymanPearson.lean)
-/
@[path]
private lemma neyman_pearson_dominated_two_simple_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {p q : Ω → ℝ}
  {k : ℝ}
  {φstar : Ω → Set.Icc (0 : ℝ) 1}
-- given
  (hp_meas : Measurable p)
  (hq_meas : Measurable q)
  (hp_nonneg : ∀ x, 0 ≤ p x)
  (hq_nonneg : ∀ x, 0 ≤ q x)
  (hp_int : Integrable p μ)
  (hq_int : Integrable q μ)
  (hk : 0 ≤ k)
  (hφstar_meas : Measurable φstar)
  (hφstar_gt : ∀ x, k * p x < q x → (φstar x).val = 1)
  (hφstar_lt : ∀ x, q x < k * p x → (φstar x).val = 0) :
-- imply
  ∀ (φ : Ω → Set.Icc (0 : ℝ) 1), Measurable φ →
    (∫ x, (φ x).val * p x ∂μ ≤ ∫ x, (φstar x).val * p x ∂μ) →
    (∫ x, (φ x).val * q x ∂μ ≤ ∫ x, (φstar x).val * q x ∂μ) := by
-- proof
  apply MathlibExt.Probability.Statistics.NeymanPearson.neyman_pearson_dominated_two_simple hp_meas hq_meas hp_nonneg hq_nonneg hp_int hq_int k hk φstar hφstar_meas hφstar_gt hφstar_lt


-- created on 2026-10-20
