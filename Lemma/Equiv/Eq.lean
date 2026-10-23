import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_epilogue
open PSet


/--
[PSet.eq_of_ofNat_equiv_ofNat](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_epilogue.lean)
-/
@[path]
private lemma main
  {n m : ℕ} :
-- imply
  (ofNat.{u} n).Equiv (ofNat.{u} m) → n = m :=
-- proof
  PSet.eq_of_ofNat_equiv_ofNat n m


-- created on 2026-10-22
