import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open Box


/--
[Box.prod_side](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ}
  {B₁: Box d₁}
  {B₂: Box d₂}
  {i : Fin (d₁ + d₂)} :
-- imply
  (B₁.prod B₂).side i =
    if h : (i : ℕ) < d₁ then B₁.side ⟨i, h⟩
    else B₂.side ⟨(i : ℕ) - d₁, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) i.isLt⟩ :=
-- proof
  Box.prod_side B₁ B₂ i


-- created on 2026-10-22
