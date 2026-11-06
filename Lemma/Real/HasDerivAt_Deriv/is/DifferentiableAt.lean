import Mathlib.Analysis.Calculus.Deriv.Basic
import Initialize.Tactic.Attr.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Real.HasDerivAt_Deriv.is.DifferentiableAt |
| comm | Real.DifferentiableAt.is.HasDerivAt_Deriv |
| mp | Real.DifferentiableAt.of.HasDerivAt_Deriv |
| mpr | Real.HasDerivAt_Deriv.of.DifferentiableAt |
-/
@[path, comm, mp, mpr]
private lemma main
  {f : ℝ → ℝ}
  {x : ℝ} :
-- imply
  HasDerivAt f (deriv f x) x ↔ DifferentiableAt ℝ f x := by
-- proof
  apply Iff.intro
  · apply HasDerivAt.differentiableAt
  · apply DifferentiableAt.hasDerivAt


-- created on 2026-11-05
