import Mathlib
import sympy.Basic
import sympy.analysis.Section_10_2
open Chapter9
open Chapter10
open Chapter10.IsLocalMinOn


/--
[IsLocalMinOn.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_2.lean)
-/
@[path]
private lemma main
  {X:Set ℝ}
  {f:ℝ → ℝ}
  {x₀:ℝ} :
-- imply
  IsLocalMinOn f X x₀ ↔
  ∃ δ > 0, IsMinOn f (X ∩ .Ioo (x₀ - δ) (x₀ + δ)) x₀ :=
-- proof
  Chapter10.IsLocalMinOn.iff X f x₀


-- created on 2026-10-22
