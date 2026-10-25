import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Sequence


/--
[Sequence.isCauchy_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a:Sequence} :
-- imply
  a.IsCauchy ↔ ∀ ε > (0:ℝ), ε.EventuallySteady a :=
-- proof
  Chapter6.Sequence.isCauchy_def a


-- created on 2026-10-22
