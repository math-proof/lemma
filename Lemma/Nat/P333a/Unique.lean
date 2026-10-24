import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.P_3_3_3a_existsUnique](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {x: Chapter3.Nat} :
-- imply
  ∃! y: Chapter3.Nat, P_3_3_3a x y :=
-- proof
  by
    apply ExistsUnique.intro ((x+1:ℕ):Chapter3.Nat)
    ·
      simp [P_3_3_3a]
    intro y h
    apply (nat_equiv_symm_inj y (((x + 1 : ℕ) : Chapter3.Nat))).mp
    simpa [P_3_3_3a, nat_equiv_coe_of_coe] using h


-- created on 2026-10-22
-- updated on 2026-10-23
