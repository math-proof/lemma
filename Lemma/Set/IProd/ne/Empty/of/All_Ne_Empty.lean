import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_3_5.Part9
open Chapter3.SetTheory.Set hiding Fin
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.finite_choice](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n:ℕ}
  {X: Chapter3.SetTheory.Set.Fin n → Chapter3.Set}
-- given
  (h: ∀ i, X i ≠ ∅) :
-- imply
  iProd X ≠ ∅ :=
-- proof
  Chapter3.SetTheory.Set.finite_choice h


-- created on 2026-10-22
