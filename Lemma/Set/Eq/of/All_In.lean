import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_1
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.ext](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set}
-- given
  (h: ∀ x, x ∈ X ↔ x ∈ Y) :
-- imply
  X = Y :=
-- proof
  extensionality _ _ h


-- created on 2026-10-22
-- updated on 2026-10-23
