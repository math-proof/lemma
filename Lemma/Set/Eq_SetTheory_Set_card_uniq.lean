import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_6
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.card_uniq](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X:Chapter3.Set}
  {n m:ℕ}
-- given
  (h0: X.has_card n)
  (h1: X.has_card m) :
-- imply
  n = m :=
-- proof
  Chapter3.SetTheory.Set.card_uniq h0 h1


-- created on 2026-10-22
