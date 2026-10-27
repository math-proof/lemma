import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.Real
open Chapter5.Real.LIM


/--
[Real.LIM.zero](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  :
-- imply
  LIM (fun _ ↦ (0:ℚ)) = 0 :=
-- proof
  Chapter5.Real.LIM.zero


-- created on 2026-10-22
