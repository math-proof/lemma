import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open Box


/--
[Box.prod_toSet](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ}
  {B₁: Box d₁}
  {B₂: Box d₂} :
-- imply
  EuclideanSpace'.prod B₁.toSet B₂.toSet = (B₁.prod B₂).toSet :=
-- proof
  Box.prod_toSet B₁ B₂


-- created on 2026-10-22
