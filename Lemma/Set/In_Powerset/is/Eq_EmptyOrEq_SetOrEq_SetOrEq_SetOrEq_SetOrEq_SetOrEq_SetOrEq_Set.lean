import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_4
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.powerset_of_triple](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {a b c x:Object} :
-- imply
  x ∈ powerset {a,b,c}
    ↔ x = (∅:Chapter3.Set)
      ∨ x = ({a}:Chapter3.Set)
      ∨ x = ({b}:Chapter3.Set)
      ∨ x = ({c}:Chapter3.Set)
      ∨ x = ({a,b}:Chapter3.Set)
      ∨ x = ({a,c}:Chapter3.Set)
      ∨ x = ({b,c}:Chapter3.Set)
      ∨ x = ({a,b,c}:Chapter3.Set) :=
-- proof
  Chapter3.SetTheory.Set.powerset_of_triple a b c x


-- created on 2026-10-22
