import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_11_8.Part7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[left_lim_of_continuous](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {X:Set ℝ}
  {f: ℝ → ℝ}
  {x₀:ℝ}
-- given
  (h : ∃ ε>0, .Ioc (x₀-ε) x₀ ⊆ X)
  (hf: ContinuousWithinAt f X x₀) :
-- imply
  left_lim f x₀ = f x₀ :=
-- proof
  Chapter11.left_lim_of_continuous h hf


-- created on 2026-10-22
