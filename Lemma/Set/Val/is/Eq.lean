import Mathlib
import sympy.Basic
import Instance.Analysis.Section_3_1.Part5
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.coe_inj](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {A:Chapter3.Set}
  {x y:A} :
-- imply
  x.val = y.val ↔ x = y :=
-- proof
  Subtype.coe_inj


-- created on 2026-10-22
-- updated on 2026-10-23
