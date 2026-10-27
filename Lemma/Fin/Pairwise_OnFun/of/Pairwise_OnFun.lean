import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open AlmostDisjoint


/--
[AlmostDisjoint.restrict_fin](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {B : ℕ → Box d}
  {N : ℕ}
-- given
  (h : Pairwise (Function.onFun AlmostDisjoint B)) :
-- imply
  Pairwise (Function.onFun AlmostDisjoint (fun i : Fin N => B i.val)) :=
-- proof
  AlmostDisjoint.restrict_fin h N


-- created on 2026-10-22
