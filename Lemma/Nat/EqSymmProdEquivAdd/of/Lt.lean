import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open EuclideanSpace'


/--
[EuclideanSpace'.prod_equiv_symm_apply_right](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ}
  {y : EuclideanSpace' d₁}
  {z : EuclideanSpace' d₂}
  {j : ℕ}
-- given
  (hj : j < d₂) :
-- imply
  (EuclideanSpace'.prod_equiv d₁ d₂).symm (y, z) ⟨d₁ + j, Nat.add_lt_add_left hj d₁⟩ =
      z ⟨j, hj⟩ :=
-- proof
  EuclideanSpace'.prod_equiv_symm_apply_right y z hj


-- created on 2026-10-22
