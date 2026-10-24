import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_1
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Object


/--
[SetTheory.Object.ofnat_eq'''](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n:ℕ}
  {hn} :
-- imply
  ((⟨(n:Object), hn⟩: nat): ℕ) = n :=
-- proof
  by
    simp [Nat.cast, NatCast.natCast, Equiv.symm_apply_apply]


-- created on 2026-10-22
-- updated on 2026-10-23
