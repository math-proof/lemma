import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Appendix_B_1.Part6
open AppendixB
open AppendixB.Digit


/--
[Digit.toNat_mk](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {n:ℕ}
-- given
  (h: n < 10) :
-- imply
  (Digit.mk h:ℕ) = n :=
-- proof
  AppendixB.Digit.toNat_mk h


-- created on 2026-10-22
