import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Appendix_B_1.Part6
open AppendixB
open AppendixB.PosintDecimal


/--
[PosintDecimal.append_toNat](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {p:PosintDecimal}
  {d:Digit} :
-- imply
  (p.append d:ℕ) = d.toNat + 10 * p.toNat :=
-- proof
  AppendixB.PosintDecimal.append_toNat p d


-- created on 2026-10-22
