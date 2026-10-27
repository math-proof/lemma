import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.Sequence
open Chapter5.Sequence.IsCauchy


/--
[Sequence.IsCauchy.add](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a b:ℕ → ℚ}
-- given
  (ha: (a:Sequence).IsCauchy)
  (hb: (b:Sequence).IsCauchy) :
-- imply
  (a + b:Sequence).IsCauchy :=
-- proof
  Chapter5.Sequence.IsCauchy.add ha hb


-- created on 2026-10-22
