import Mathlib
import sympy.Basic
import Instance.Analysis.Section_3_1.Part5
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.subtype_property](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {A:Chapter3.Set}
  {x:A} :
-- imply
  x.val ∈ A :=
-- proof
  x.property


-- created on 2026-10-22
-- updated on 2026-10-23
