import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_epilogue
open PSet


/--
[PSet.mem_ofNat_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_epilogue.lean)
-/
@[path]
private lemma main
  {n m : ℕ} :
-- imply
  ofNat n ∈ ofNat m ↔ n < m :=
-- proof
  PSet.mem_ofNat_iff n m


-- created on 2026-10-22
