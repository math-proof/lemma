import Mathlib
import sympy.Basic
import Abbrev.Analysis.Appendix_B_1.Part6
open AppendixB
open AppendixB.PosintDecimal


/--
[PosintDecimal.coe_inj](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {p q:PosintDecimal} :
-- imply
  (p:ℕ) = (q:ℕ) ↔ p = q :=
-- proof
  AppendixB.PosintDecimal.coe_inj p q


-- created on 2026-10-22
