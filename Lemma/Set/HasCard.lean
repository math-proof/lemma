import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_3_6.Part5
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.EquivCard_to_has_card_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set}
  {n: ℕ}
-- given
  (h: X ≈ Y) :
-- imply
  X.has_card n ↔ Y.has_card n :=
-- proof
  Chapter3.SetTheory.Set.EquivCard_to_has_card_eq h


-- created on 2026-10-22
