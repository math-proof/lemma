import Def.Analysis.Real.Limits.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ : ℝ} :
-- imply
  Filter.limUnder (nhdsWithin x₀ {x₀}ᶜ) f =
    Filter.limUnder (nhdsWithin x₀ {x₀}ᶜ) fun y => f y := by
-- proof
  rfl


-- created on 2020-04-06
