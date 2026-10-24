import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_5
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.OrderedPair


/--
[OrderedPair.eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {x y x' y' : Object} :
-- imply
  (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' :=
-- proof
  Chapter3.OrderedPair.eq x y x' y'


-- created on 2026-10-22
