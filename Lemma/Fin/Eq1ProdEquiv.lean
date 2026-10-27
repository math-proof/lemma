import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open EuclideanSpace'


/--
[EuclideanSpace'.prod_equiv_apply_fst](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ}
  {x : EuclideanSpace' (d₁ + d₂)}
  {i : Fin d₁} :
-- imply
  (EuclideanSpace'.prod_equiv d₁ d₂ x).1 i = x ⟨i, Nat.lt_add_right d₂ i.isLt⟩ :=
-- proof
  EuclideanSpace'.prod_equiv_apply_fst x i


-- created on 2026-10-22
