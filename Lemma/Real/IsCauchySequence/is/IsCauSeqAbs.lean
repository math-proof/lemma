import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_6_epilogue.Part2
open Filter
open Chapter6
open Chapter6.Sequence


/--
[Chapter6.Sequence.isCauchy_iff_isCauSeq](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_epilogue.lean)
-/
@[path]
private lemma main
  {a: ℕ → ℝ} :
-- imply
  (a:Sequence).IsCauchy ↔ IsCauSeq _root_.abs a :=
-- proof
  Chapter6.Sequence.isCauchy_iff_isCauSeq a


-- created on 2026-10-22
