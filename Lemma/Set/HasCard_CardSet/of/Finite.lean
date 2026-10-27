import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_3_6.Part5
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.has_card_card](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X:Chapter3.Set}
-- given
  (hX: X.finite) :
-- imply
  X.has_card (SetTheory.Set.card X) :=
-- proof
  Chapter3.SetTheory.Set.has_card_card hX


-- created on 2026-10-22
