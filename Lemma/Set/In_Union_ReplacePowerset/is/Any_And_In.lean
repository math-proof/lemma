import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_3_4.Part8
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.mem_union_powerset_replace_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {S : Chapter3.Set}
  {P : S.powerset → Object → Prop}
  {hP : _}
  {x : Object} :
-- imply
  x ∈ union (S.powerset.replace (P := P) hP) ↔
  ∃ (S' : S.powerset) (U : Set), P S' U ∧ x ∈ U :=
-- proof
  Chapter3.SetTheory.Set.mem_union_powerset_replace_iff


-- created on 2026-10-22
