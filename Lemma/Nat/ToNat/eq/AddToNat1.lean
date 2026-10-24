import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_epilogue


/--
[succ_toNat](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_epilogue.lean)
-/
@[path]
private lemma main
  {n : Chapter2.Nat} :
-- imply
  (n++).toNat = n.toNat + 1 :=
-- proof
  rfl


-- created on 2026-10-20
-- updated on 2026-10-23
