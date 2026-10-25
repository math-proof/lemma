import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_2.Part2
open Chapter5
open Chapter5.Rat


/--
[Rat.eventuallyClose_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_2.lean)
-/
@[path]
private lemma main
  {ε: ℚ}
  {a b: Sequence} :
-- imply
  ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) :=
-- proof
  Chapter5.Rat.eventuallyClose_def ε a b


-- created on 2026-10-22
