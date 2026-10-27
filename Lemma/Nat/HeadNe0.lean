import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Appendix_B_1.Part6
open AppendixB
open AppendixB.PosintDecimal


/--
[PosintDecimal.head_ne_zero'](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {p:PosintDecimal} :
-- imply
  (p.head:ℕ) ≠ 0 :=
-- proof
  AppendixB.PosintDecimal.head_ne_zero' p


-- created on 2026-10-22
