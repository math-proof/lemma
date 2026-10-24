import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_4
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.mem_preimage](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set}
  {f:X → Y}
  {U: Chapter3.Set}
  {x:X} :
-- imply
  x.val ∈ preimage f U ↔ (f x).val ∈ U :=
-- proof
  Chapter3.SetTheory.Set.mem_preimage f U x


-- created on 2026-10-22
