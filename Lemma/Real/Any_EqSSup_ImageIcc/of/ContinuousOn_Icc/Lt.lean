import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_9_6
open Chapter9
open Chapter9.sSup


/--
[sSup.of_continuous_on_compact](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_6.lean)
-/
@[path]
private lemma main
  {a b:ℝ}
  {f:ℝ → ℝ}
-- given
  (h:a < b)
  (hf: ContinuousOn f (.Icc a b)) :
-- imply
  ∃ xmax ∈ Set.Icc a b, sSup (f '' .Icc a b) = f xmax :=
-- proof
  Chapter9.sSup.of_continuous_on_compact h f hf


-- created on 2026-10-22
