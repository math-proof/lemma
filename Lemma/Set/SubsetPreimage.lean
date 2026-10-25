import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_3_4.Part8
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.preimage_in_domain](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set}
  {f:X → Y}
  {U: Chapter3.Set} :
-- imply
  (preimage f U) ⊆ X :=
-- proof
  Chapter3.SetTheory.Set.preimage_in_domain f U


-- created on 2026-10-22
