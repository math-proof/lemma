import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_4
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.preimage_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set}
  {f:X → Y}
  {U: Chapter3.Set} :
-- imply
  ((preimage f U): _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) :=
-- proof
  Chapter3.SetTheory.Set.preimage_eq f U


-- created on 2026-10-22
