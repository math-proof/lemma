import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_3_1.Part5
import Lemma.Set.Eq.of.Object
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Set


/--
[SetTheory.Set.coe_eq_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set} :
-- imply
  (X: Object) = (Y: Object) ↔  X = Y :=
-- proof
  ⟨ Eq.of.Object, by rintro rfl; rfl ⟩


-- created on 2026-10-22
-- updated on 2026-10-26
