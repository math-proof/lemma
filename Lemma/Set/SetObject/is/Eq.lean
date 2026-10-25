import Mathlib
import sympy.Basic
import Instance.Analysis.Section_3_1.Part5
import Lemma.Set.Eq.of.All_In
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Set


/--
[SetTheory.Set.coe_inj'](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set} :
-- imply
  (X : _root_.Set Object) = (Y : _root_.Set Object) ↔ X = Y :=
-- proof
  by
    constructor
    ·
      intro h
      apply Eq.of.All_In
      intro x
      replace h := congr(x ∈ $h)
      simpa using h
    rintro rfl; rfl


-- created on 2026-10-22
-- updated on 2026-10-23
