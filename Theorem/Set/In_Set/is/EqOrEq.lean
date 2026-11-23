module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_3_1.Part5
public import Theorem.Set.In_Set.is.Eq
public import Theorem.Set.In_Union.is.InOrIn
public import Theorem.Set.Set.eq.Union

public section

open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Set


/--
[SetTheory.Set.mem_pair](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
public theorem main
  [SetTheory]
  {x a b:Object} :
-- imply
  x ∈ ({a,b}:Chapter3.Set) ↔ (x = a ∨ x = b) :=
-- proof
  by
    simp [Set.eq.Union, In_Union.is.InOrIn, In_Set.is.Eq]


-- created on 2026-10-22
-- updated on 2026-10-26
