import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Pointwise
open EuclideanSpace'


/--
[EuclideanSpace'.prod_equiv_apply_snd](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ}
  {x : EuclideanSpace' (d₁ + d₂)}
  {j : Fin d₂} :
-- imply
  (EuclideanSpace'.prod_equiv d₁ d₂ x).2 j =
      x ⟨(j : ℕ) + d₁, by omega⟩ :=
-- proof
  EuclideanSpace'.prod_equiv_apply_snd x j


-- created on 2026-10-22
