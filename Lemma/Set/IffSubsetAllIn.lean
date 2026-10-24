import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_1
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.subset_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set} :
-- imply
  X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y :=
-- proof
  by rfl


-- created on 2026-10-22
-- updated on 2026-10-23
