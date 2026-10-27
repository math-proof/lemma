import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.CauchySequence


/--
[CauchySequence.coe_to_sequence](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a: CauchySequence} :
-- imply
  ((a:ℕ → ℚ):Sequence) = a.toSequence :=
-- proof
  Chapter5.CauchySequence.coe_to_sequence a


-- created on 2026-10-22
