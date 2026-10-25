import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_3_4.Part8
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.mem_image](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set}
  {f:X → Y}
  {S: Chapter3.Set}
  {y:Object} :
-- imply
  y ∈ image f S ↔ ∃ x:X, x.val ∈ S ∧ f x = y :=
-- proof
  Chapter3.SetTheory.Set.mem_image f S y


-- created on 2026-10-22
