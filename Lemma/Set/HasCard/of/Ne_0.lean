import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_3_6.Part5
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.card_to_has_card](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X:Chapter3.Set}
  {n: ℕ}
-- given
  (hn: n ≠ 0) :
-- imply
  X.card = n → X.has_card n :=
-- proof
  Chapter3.SetTheory.Set.card_to_has_card hn


-- created on 2026-10-22
