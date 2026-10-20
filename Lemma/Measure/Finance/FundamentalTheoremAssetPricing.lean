import Mathlib
import sympy.Basic
import sympy.atlas.Probability.Finance.FundamentalTheoremAssetPricing
open MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing


/--
[one_period_fundamental_theorem_asset_pricing_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Finance/FundamentalTheoremAssetPricing.lean)
-/
@[path]
private lemma one_period_fundamental_theorem_asset_pricing_general_eq
  [Fintype Ω] [Nonempty Ω] [Fintype A]
  {g : A → Ω → ℝ} :
-- imply
  (¬ ∃ h : A → ℝ, (∀ ω : Ω, 0 ≤ ∑ a : A, h a * g a ω) ∧
    (∃ ω : Ω, 0 < ∑ a : A, h a * g a ω)) ↔
    ∃ q : Ω → ℝ, (∀ ω : Ω, 0 < q ω) ∧ (∑ ω : Ω, q ω = 1) ∧
    (∀ a : A, ∑ ω : Ω, q ω * g a ω = 0) := by
-- proof
  apply MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing.one_period_fundamental_theorem_asset_pricing_general g

/--
[one_period_fundamental_theorem_asset_pricing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Finance/FundamentalTheoremAssetPricing.lean)
-/
@[path]
private lemma one_period_fundamental_theorem_asset_pricing_eq
  [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [Fintype A] [DecidableEq A]
  {g : A → Ω → ℝ} :
-- imply
  (¬ ∃ h : A → ℝ, (∀ ω : Ω, 0 ≤ ∑ a : A, h a * g a ω) ∧
    (∃ ω : Ω, 0 < ∑ a : A, h a * g a ω)) ↔
    ∃ q : Ω → ℝ, (∀ ω : Ω, 0 < q ω) ∧ (∑ ω : Ω, q ω = 1) ∧
    (∀ a : A, ∑ ω : Ω, q ω * g a ω = 0) := by
-- proof
  apply MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing.one_period_fundamental_theorem_asset_pricing g


-- created on 2026-10-20
