import Mathlib
import sympy.Basic
import Instance.Analysis.Section_3_1.Part5
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.replacement_axiom](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {A:Chapter3.Set}
  {P: A → Object → Prop}
  {y:Object}
-- given
  (hP: ∀ x y y', P x y ∧ P x y' → y = y') :
-- imply
  y ∈ A.replace hP ↔ ∃ x, P x y :=
-- proof
  SetTheory.replacement_axiom A P hP y


-- created on 2026-10-22
-- updated on 2026-10-23
