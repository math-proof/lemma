import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_11_8.Part7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[right_lim_le_left_lim_of_monotone](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {a b:ℝ}
-- given
  (hab: a < b)
  (hf: Monotone f) :
-- imply
  right_lim f a ≤ left_lim f b :=
-- proof
  Chapter11.right_lim_le_left_lim_of_monotone hab hf


-- created on 2026-10-22
