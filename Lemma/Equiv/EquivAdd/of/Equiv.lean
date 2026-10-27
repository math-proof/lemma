import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.Sequence


/--
[Sequence.add_equiv_right](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {b b' a : ℕ → ℚ}
-- given
  (hbb': Equiv b b') :
-- imply
  Equiv (a + b) (a + b') :=
-- proof
  Chapter5.Sequence.add_equiv_right a hbb'


-- created on 2026-10-22
