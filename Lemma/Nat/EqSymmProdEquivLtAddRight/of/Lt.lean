import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open EuclideanSpace'


/--
[EuclideanSpace'.prod_equiv_symm_apply_left](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ}
  {y : EuclideanSpace' d₁}
  {z : EuclideanSpace' d₂}
  {i : ℕ}
-- given
  (hi : i < d₁) :
-- imply
  (EuclideanSpace'.prod_equiv d₁ d₂).symm (y, z) ⟨i, Nat.lt_add_right d₂ hi⟩ = y ⟨i, hi⟩ :=
-- proof
  EuclideanSpace'.prod_equiv_symm_apply_left y z hi


-- created on 2026-10-22
