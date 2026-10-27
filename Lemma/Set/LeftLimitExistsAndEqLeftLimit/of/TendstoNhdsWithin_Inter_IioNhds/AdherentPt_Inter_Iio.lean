import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_9_5.Part2
open Chapter9
open Chapter9.left_limit


/--
[left_limit.eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_5.lean)
-/
@[path]
private lemma main
  {X: Set ℝ}
  {f: ℝ → ℝ}
  {x₀ L : ℝ}
-- given
  (had: AdherentPt x₀ (X ∩ .Iio x₀))
  (h: (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds L)) :
-- imply
  LeftLimitExists X f x₀ ∧ left_limit X f x₀ = L :=
-- proof
  Chapter9.left_limit.eq had h


-- created on 2026-10-22
