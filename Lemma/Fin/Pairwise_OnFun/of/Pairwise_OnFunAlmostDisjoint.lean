import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open AlmostDisjoint


/--
[AlmostDisjoint.pairwise_castSucc](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d n : ℕ}
  {B : Fin (n + 1) → Box d}
-- given
  (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) :
-- imply
  Pairwise (Function.onFun AlmostDisjoint (fun i => B (Fin.castSucc i))) :=
-- proof
  AlmostDisjoint.pairwise_castSucc hdisj


-- created on 2026-10-22
