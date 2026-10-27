import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_8_1.Part4
open Chapter8
open Chapter8.Nat


/--
[Nat.countable_of_infinite](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  {X : Set ℕ} [Infinite X] :
-- imply
  CountablyInfinite X :=
-- proof
  Chapter8.Nat.countable_of_infinite X


-- created on 2026-10-22
