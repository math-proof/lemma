import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_8_4
open Chapter8


/--
[axiom_of_countable_choice](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_4.lean)
-/
@[path]
private lemma main
  {I: Type} [Countable I]
  {X: I → Type}
-- given
  (h : ∀ i, Nonempty (X i)) :
-- imply
  Nonempty (∀ i, X i) :=
-- proof
  Chapter8.axiom_of_countable_choice h


-- created on 2026-10-22
