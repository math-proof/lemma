import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Appendix_B_1.Part6
open AppendixB
open AppendixB.PosintDecimal


/--
[PosintDecimal.digit_eq](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {d:Digit}
-- given
  (h: d ≠ 0) :
-- imply
  (mk' d [] h:ℕ) = d :=
-- proof
  AppendixB.PosintDecimal.digit_eq h


-- created on 2026-10-22
