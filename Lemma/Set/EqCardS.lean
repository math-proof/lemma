import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_3_6.Part5
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.card_eq_nat_card](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X:Chapter3.Set} :
-- imply
  X.card = Nat.card X :=
-- proof
  Chapter3.SetTheory.Set.card_eq_nat_card


-- created on 2026-10-22
