import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_6_4.Part3
open EReal
open Chapter6
open Chapter6.Sequence


/--
[Sequence.Cauchy_iff_convergent](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean)
-/
@[path]
private lemma main
  {a:Sequence} :
-- imply
  a.IsCauchy ↔ a.Convergent :=
-- proof
  Chapter6.Sequence.Cauchy_iff_convergent a


-- created on 2026-10-22
