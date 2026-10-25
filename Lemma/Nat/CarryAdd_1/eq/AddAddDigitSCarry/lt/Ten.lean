import Mathlib
import sympy.Basic
import Abbrev.Analysis.Appendix_B_1.Part6
open AppendixB
open AppendixB.PosintDecimal


/--
[PosintDecimal.carry_succ](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {p q:PosintDecimal}
  {i:ℕ} :
-- imply
  p.carry q (i+1) = if ((p.digit i:ℕ) + (q.digit i:ℕ) + p.carry q i < 10) then 0 else 1 :=
-- proof
  AppendixB.PosintDecimal.carry_succ p q i


-- created on 2026-10-22
