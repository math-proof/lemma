import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Appendix_A_7.Part2


/--
[is_coe](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_A_7.lean)
-/
@[path]
private lemma main
  {N:NewInt} :
-- imply
  ∃ n:ℤ, N = (n:NewInt) :=
-- proof
  NewInt.is_coe N


-- created on 2026-10-20
