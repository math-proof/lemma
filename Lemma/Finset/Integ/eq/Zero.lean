import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_4
open UnsignedSimpleFunction


/--
[UnsignedSimpleFunction.integ_zero](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  let h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
    use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
    exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
  h_simple.integ = 0 :=
-- proof
  UnsignedSimpleFunction.integ_zero


-- created on 2026-10-22
