import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.P_3_3_5_existsUnique](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {x: Chapter3.Nat} :
-- imply
  ∃! y: Chapter3.Nat, P_3_3_5 x y :=
-- proof
  by
    apply ExistsUnique.intro 7 <;> simp [P_3_3_5]


-- created on 2026-10-22
-- updated on 2026-10-23
