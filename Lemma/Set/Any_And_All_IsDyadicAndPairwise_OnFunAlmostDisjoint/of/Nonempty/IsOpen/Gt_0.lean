import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open IsOpen


/--
[IsOpen.eq_union_boxes](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hd : 0 < d)
  (hE: IsOpen E)
  (hE_nonempty : E.Nonempty) :
-- imply
  ∃ B: ℕ → Box d, (E = ⋃ n, (B n).toSet) ∧ (∀ n, (B n).IsDyadic) ∧
      Pairwise (Function.onFun AlmostDisjoint B) :=
-- proof
  IsOpen.eq_union_boxes hd E hE hE_nonempty


-- created on 2026-10-22
