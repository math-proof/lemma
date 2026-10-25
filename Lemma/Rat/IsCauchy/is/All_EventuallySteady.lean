import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_1.Part9
open Chapter5


/--
[isCauchy_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {a:Sequence} :
-- imply
  a.IsCauchy ↔ ∀ ε > (0:ℚ), ε.EventuallySteady a :=
-- proof
  Chapter5.Sequence.isCauchy_def a


-- created on 2026-10-20
