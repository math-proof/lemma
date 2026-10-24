import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_epilogue
open PSet


/--
[PSet.ofNat_mem_ofNat_of_lt](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_epilogue.lean)
-/
@[path]
private lemma main
  {m n : ℕ} :
-- imply
  n < m → ofNat n ∈ ofNat m :=
-- proof
  PSet.ofNat_mem_ofNat_of_lt m n


-- created on 2026-10-22
