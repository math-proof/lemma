import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_10_2
open Chapter9
open Chapter10
open Chapter10.IsLocalMaxOn


/--
[IsLocalMaxOn.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_2.lean)
-/
@[path]
private lemma main
  {X:Set ℝ}
  {f:ℝ → ℝ}
  {x₀:ℝ} :
-- imply
  IsLocalMaxOn f X x₀ ↔
  ∃ δ > 0, IsMaxOn f (X ∩ .Ioo (x₀ - δ) (x₀ + δ)) x₀ :=
-- proof
  Chapter10.IsLocalMaxOn.iff X f x₀


-- created on 2026-10-22
