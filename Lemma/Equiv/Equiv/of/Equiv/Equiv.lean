import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.Sequence


/--
[Sequence.add_equiv](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a b a' b':ℕ → ℚ}
-- given
  (haa': Equiv a a')
  (hbb': Equiv b b') :
-- imply
  Equiv (a + b) (a' + b') :=
-- proof
  Chapter5.Sequence.add_equiv haa' hbb'


-- created on 2026-10-22
