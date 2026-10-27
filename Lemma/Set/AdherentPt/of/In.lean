import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_9_1.Part3
open Chapter9
open Chapter9.AdherentPt


/--
[AdherentPt.of_mem](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_1.lean)
-/
@[path]
private lemma main
  {X: Set ℝ}
  {x: ℝ}
-- given
  (h: x ∈ X) :
-- imply
  AdherentPt x X :=
-- proof
  Chapter9.AdherentPt.of_mem h


-- created on 2026-10-22
