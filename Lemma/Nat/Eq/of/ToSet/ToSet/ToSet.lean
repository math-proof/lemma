import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Box


/--
[Box.toSet_injective_of_nonempty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B₁ B₂ : Box d}
-- given
  (h₀ : B₁.toSet.Nonempty)
  (h₁ : B₂.toSet.Nonempty)
  (h_eq : B₁.toSet = B₂.toSet) :
-- imply
  B₁ = B₂ :=
-- proof
  Box.toSet_injective_of_nonempty h₀ h₁ h_eq


-- created on 2026-10-22
