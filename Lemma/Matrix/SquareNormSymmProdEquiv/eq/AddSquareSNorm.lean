import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open Pointwise
open EuclideanSpace'


/--
[EuclideanSpace'.norm_prod_equiv_symm](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ}
  {y : EuclideanSpace' d₁}
  {z : EuclideanSpace' d₂} :
-- imply
  ‖(EuclideanSpace'.prod_equiv d₁ d₂).symm (y, z)‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 :=
-- proof
  EuclideanSpace'.norm_prod_equiv_symm y z


-- created on 2026-10-22
