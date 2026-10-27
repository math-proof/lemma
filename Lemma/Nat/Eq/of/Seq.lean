import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.CauchySequence


/--
[CauchySequence.ext'](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a b: CauchySequence}
-- given
  (h: a.seq = b.seq) :
-- imply
  a = b :=
-- proof
  Chapter5.CauchySequence.ext' h


-- created on 2026-10-22
