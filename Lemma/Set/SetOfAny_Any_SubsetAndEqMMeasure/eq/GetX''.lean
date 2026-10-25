import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4


/--
[Jordan_inner_measure'_set_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)} :
-- imply
  { m:EReal | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A,
        A ⊆ E ∧ m = (hA.measure:EReal) }
      = (fun x:ℝ ↦ (x:EReal)) ''
          { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A,
            A ⊆ E ∧ m = hA.measure } :=
-- proof
  Jordan_inner_measure'_set_eq E


-- created on 2026-10-22
