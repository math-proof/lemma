import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open AlmostAlways


/--
[AlmostAlways.countable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {I : Type*} [Countable I]
  {d:ℕ}
  {P: I → EuclideanSpace' d → Prop}
-- given
  (hP: ∀ i, AlmostAlways (P i)) :
-- imply
  AlmostAlways (fun x ↦ ∀ i, P i x) :=
-- proof
  AlmostAlways.countable hP


-- created on 2026-10-22
