import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open Box


/--
[Box.prod_injective](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ} :
-- imply
  Function.Injective (fun p : Box d₁ × Box d₂ => p.1.prod p.2) :=
-- proof
  Box.prod_injective


-- created on 2026-10-22
