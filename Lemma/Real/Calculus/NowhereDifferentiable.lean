import Mathlib
import sympy.Basic
import sympy.Analysis.Calculus.NowhereDifferentiable

open Real.Calculus.NowhereDifferentiable

/--
[exists_continuous_nowhere_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/NowhereDifferentiable.lean)
-/
@[path]
private lemma exists_continuous_nowhere_differentiable_eq :
-- imply
  ∃ f : ContinuousMap ℝ ℝ, ∀ x, ¬ DifferentiableAt ℝ f x := by
-- proof
  apply exists_continuous_nowhere_differentiable


-- created on 2026-10-09
