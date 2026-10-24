import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_1_order
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.disjoint_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {A B:Chapter3.Set} :
-- imply
  Disjoint A B ↔ A ∩ B = ∅ :=
-- proof
  by
    convert _root_.disjoint_iff


-- created on 2026-10-22
-- updated on 2026-10-23
