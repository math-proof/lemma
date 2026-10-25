import Mathlib
import sympy.Basic
import Abbrev.Analysis.Appendix_B_1.Part6
open AppendixB
open AppendixB.PosintDecimal


/--
[PosintDecimal.exists_unique](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {n:ℕ} :
-- imply
  n > 0 → ∃! p:PosintDecimal, (p:ℕ) = n :=
-- proof
  AppendixB.PosintDecimal.exists_unique n


-- created on 2026-10-22
