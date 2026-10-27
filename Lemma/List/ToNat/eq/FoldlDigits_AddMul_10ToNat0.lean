import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Appendix_B_1.Part6
open AppendixB
open AppendixB.PosintDecimal


/--
[PosintDecimal.toNat_eq_foldl](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {q : PosintDecimal} :
-- imply
  q.toNat = q.digits.foldl (fun acc (d : Digit) => acc * 10 + d.toNat) 0 :=
-- proof
  AppendixB.PosintDecimal.toNat_eq_foldl q


-- created on 2026-10-22
