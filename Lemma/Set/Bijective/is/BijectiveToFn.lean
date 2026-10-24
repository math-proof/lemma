import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3
import Lemma.Set.OneToOne.is.InjectiveToFn
import Lemma.Set.Onto.is.SurjectiveToFn
open Chapter3 hiding Nat Set
open Chapter3.Function
open Set


/--
[Function.bijective_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y: Chapter3.Set}
  {f: Function X Y} :
-- imply
  f.bijective ↔ Function.Bijective f.to_fn :=
-- proof
  by
    rw [Function.bijective, Function.Bijective, OneToOne.is.InjectiveToFn, Onto.is.SurjectiveToFn]


-- created on 2026-10-22
-- updated on 2026-10-23
