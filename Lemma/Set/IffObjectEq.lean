import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_4
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.coe_of_fun_inj](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set}
  {f g:X → Y} :
-- imply
  (f:Object) = (g:Object) ↔ f = g :=
-- proof
  Chapter3.SetTheory.Set.coe_of_fun_inj f g


-- created on 2026-10-22
