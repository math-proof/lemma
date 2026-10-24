import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Analysis.FunctionalAnalysis.BanachLimit
open Filter
open scoped BoundedContinuousFunction ContinuousLinearMap


namespace MathlibExt.Analysis.FunctionalAnalysis.BanachLimitTest

/--
[witness_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/FunctionalAnalysis/BanachLimit.lean)
-/
@[path]
private lemma witness_spec :
  (∀ f : ℕ →ᵇ ℝ, (∀ n, 0 ≤ f n) → 0 ≤ witness f) ∧
  witness (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1 ∧
  (∀ f g : ℕ →ᵇ ℝ, (∀ n, g n = f (n + 1)) → witness f = witness g) ∧
  (∀ f : ℕ →ᵇ ℝ, ∀ l : ℝ,
    Tendsto (fun n => f n) atTop (nhds l) → witness f = l) :=
  Classical.choose_spec MathlibExt.Analysis.FunctionalAnalysis.BanachLimit.banach_limit

end MathlibExt.Analysis.FunctionalAnalysis.BanachLimitTest


-- created on 2026-10-23
