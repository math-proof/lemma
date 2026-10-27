import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Appendix_B_1.Part6
open AppendixB
open AppendixB.Digit


/--
[Digit.eq](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {n: Digit} :
-- imply
  n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 :=
-- proof
  AppendixB.Digit.eq n


-- created on 2026-10-22
