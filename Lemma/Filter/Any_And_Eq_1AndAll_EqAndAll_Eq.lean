import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.NormedSpace.BanachLimit.Part5

/--
[BanachLimit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/BanachLimit.lean)
-/
@[path]
private lemma banach_limit_is :
-- imply
  ∃ L : BoundedContinuousFunction ℕ ℝ →L[ℝ] ℝ,
    (∀ f : BoundedContinuousFunction ℕ ℝ, (∀ n, 0 ≤ f n) → 0 ≤ L f) ∧
    L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1 ∧
    (∀ (f g : BoundedContinuousFunction ℕ ℝ), (∀ n, g n = f (n + 1)) → L f = L g) ∧
    (∀ (f : BoundedContinuousFunction ℕ ℝ) (l : ℝ),
      Filter.Tendsto (fun n => f n) Filter.atTop (nhds l) → L f = l) := by
-- proof
  apply FunctionalAnalysis.BanachLimit.banach_limit

-- created on 2026-10-10
