import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_3_6.Part5
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.empty_of_card_eq_zero](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X:Chapter3.Set}
-- given
  (hX : X.finite) :
-- imply
  X.card = 0 → X = ∅ :=
-- proof
  Chapter3.SetTheory.Set.empty_of_card_eq_zero hX


-- created on 2026-10-22
