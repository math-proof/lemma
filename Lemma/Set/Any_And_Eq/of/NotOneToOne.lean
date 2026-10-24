import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.two_to_one](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y: Chapter3.Set}
  {f: Function X Y}
-- given
  (h: ¬ f.one_to_one) :
-- imply
  ∃ x x': X, x ≠ x' ∧ f x = f x' :=
-- proof
  by
    rw [Function.one_to_one] at h; aesop


-- created on 2026-10-22
-- updated on 2026-10-23
