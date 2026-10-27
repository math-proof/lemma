import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.ratCast_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {q:ℚ} :
-- imply
  (q:Chapter5.Real) = LIM (fun _ ↦ q) :=
-- proof
  Chapter5.Real.ratCast_def q


-- created on 2026-10-22
