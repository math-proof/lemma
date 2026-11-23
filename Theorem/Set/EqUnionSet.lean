module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_3_1.Part5
public import Theorem.Set.Eq.of.All_In
public import Theorem.Set.In_Set.is.EqOrEqOrEq
public import Theorem.Set.In_Union.is.InOrIn
public import Theorem.Set.In_Set.is.EqOrEq

public section

open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Set


/--
[SetTheory.Set.pair_union_pair](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
public theorem main
  [SetTheory]
  {a b c:Object} :
-- imply
  ({a,b}:Chapter3.Set) ∪ {b,c} = {a,b,c} :=
-- proof
  by
    apply Eq.of.All_In; intro; simp only [In_Union.is.InOrIn, In_Set.is.EqOrEq, In_Set.is.EqOrEqOrEq]; tauto


-- created on 2026-10-22
-- updated on 2026-10-26
