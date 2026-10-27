import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open AlmostDisjoint


/--
[AlmostDisjoint.castSucc_last](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d n : ℕ}
  {B : Fin (n + 1) → Box d}
  {i : Fin n}
-- given
  (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) :
-- imply
  AlmostDisjoint (B (Fin.castSucc i)) (B (Fin.last n)) :=
-- proof
  AlmostDisjoint.castSucc_last hdisj i


-- created on 2026-10-22
