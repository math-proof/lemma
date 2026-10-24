import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_6
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.EquivCard_to_card_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set}
-- given
  (h: X ≈ Y) :
-- imply
  X.card = Y.card :=
-- proof
  Chapter3.SetTheory.Set.EquivCard_to_card_eq h


-- created on 2026-10-22
